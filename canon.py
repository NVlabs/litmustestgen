#!/usr/bin/env python

# Automated Synthesis of Comprehensive Memory Model Litmus Test Suites
# Daniel Lustig, Andrew Wright, Alexandros Papakonstantinou, Olivier Giroux
# ASPLOS 2017
#
# Copyright (c) 2017, NVIDIA Corporation.  All rights reserved.
#
# This file is licensed under the BSD-3 license.  See LICENSE for details.

import sys
import re
import xml.etree.ElementTree as ET

# a single node in an Alloy instance
class Atom:
  def __init__(self, label, sig_label):
    self._label = label
    self._sig_label = sig_label
  def __repr__(self):
    "just list all the properties"
    d = {}
    for a in dir(self): # guaranteed to be alphabetical
      if a[:2] != "__":
        d[a] = getattr(self, a)
    return str(d)

instances = {}
unique = 0
total = 0
last = 0

def follow_edge(atom, edge):
  "Return atom.edge.  There should only be one choice"
  candidates = []
  if not hasattr(atom, edge):
    return None
  for c in getattr(atom, edge):
    candidates.append(c)
  if len(candidates) != 1:
    raise Exception("multiple %s edges?" % edge)
  return candidates[0]

def follow_edge_tr(atoms, atom, edge):
  "like follow_edge, but for transitively closed relations"
  candidates = []
  if not hasattr(atom, edge):
    return None
  # first, add all adjacent atoms
  for c in getattr(atom, edge):
    candidates.append(c)
  # now, prune out all atoms which are at least two steps away
  for c1 in getattr(atom, edge):
    a1 = atoms[c1]
    if hasattr(a1, edge):
      for c2 in getattr(a1, edge):
        if c2 in candidates:
          candidates.remove(c2)
  # there should only be one candidate lett
  if len(candidates) != 1:
    raise Exception("multiple %s edges?" % edge)
  return candidates[0]

def follow_po_edge(atoms, atom):
  "like follow_edge, but for po or sb specifically"
  x = follow_edge(atom, "po")
  if x:
    return x
  x = follow_edge_tr(atoms, atom, "sb")
  if x:
    return x
  return None

event_hash_dict = {
    "Read": "R",
    "Write": "W",
    "Acquire": "Aq",
    "Release": "Rl",
    "Fence": "F",
    "FenceAll": "Far",
    "FenceAcqRel": "Far",
    "FenceAcq": "Faq",
    "FenceRel": "Frl",
    "FenceSC": "Fsc",
    "Branch": "Br",
    "lwsync": "L",
    "sync": "S",
    "CtrlFence": "C",
    "AtomicRead": "AR",
    "AtomicWrite": "AW",
    "AtomicRMW": "AA",
    "RMW": "AA",
    "NonAtomicRead": "NR",
    "NonAtomicWrite": "NW",
}

memory_order_dict = {
    "MemoryOrderSeqCst$0": "sc",
    "MemoryOrderAcqRel$0": "ar",
    "MemoryOrderRelease$0": "rl",
    "MemoryOrderAcquire$0": "aq",
    "MemoryOrderRelaxed$0": "rx",
    "MemoryOrderNonAtomic$0": "na"
}

def event_hash_without_addr(thread, atom):
  "Get a hash of the event.  The address is calculated elsewhere in globally sorted order"
  if not hasattr(thread, "_memo"):
    thread._memo = {}

  # check if we've already calculated this hash
  if atom._label in thread._memo:
    return thread._memo[atom._label]

  # we haven't already calculated this hash, so start generating it
  if not hasattr(thread, "_addr_dep_dsts"):
    thread._addr_dep_dsts = {}
  if not hasattr(thread, "_ctrl_dep_dsts"):
    thread._ctrl_dep_dsts = {}
  if not hasattr(thread, "_data_dep_dsts"):
    thread._data_dep_dsts = {}
  if not hasattr(thread, "_next_dep_source_id"):
    thread._next_dep_source_id = 0

  # start with the event itself
  s = "_" + event_hash_dict[atom._sig_label]

  # memory order, in C/C++
  if hasattr(atom, "memory_order"):
    s += memory_order_dict[follow_edge(atom, "memory_order")]

  # if this atom is the source of an address dependency
  if hasattr(atom, "addr"):
    dep_source_id = thread._next_dep_source_id
    s += "s" + str(dep_source_id)
    thread._next_dep_source_id += 1
    for addr in atom.addr:
      thread._addr_dep_dsts[addr] = dep_source_id

  # if this atom is the target of an address dependency
  if atom._label in thread._addr_dep_dsts:
    req = thread._addr_dep_dsts[atom._label]
    s += "ra" + str(req)

  # if this atom is the source of a control dependency
  if hasattr(atom, "ctrl"):
    if not hasattr(thread, "_next_dep_source_id"):
      thread._next_dep_source_id = 0
    dep_source_id = thread._next_dep_source_id
    s += "s" + str(dep_source_id)
    thread._next_dep_source_id += 1
    for ctrl in atom.ctrl:
      thread._ctrl_dep_dsts[ctrl] = dep_source_id

  # if this atom is the target of a control dependency
  if atom._label in thread._ctrl_dep_dsts:
    req = thread._ctrl_dep_dsts[atom._label]
    s += "rc" + str(req)

  # if this atom is the source of a data dependency
  if hasattr(atom, "data"):
    if not hasattr(thread, "_next_dep_source_id"):
      thread._next_dep_source_id = 0
    dep_source_id = thread._next_dep_source_id
    s += "s" + str(dep_source_id)
    thread._next_dep_source_id += 1
    for data in atom.data:
      thread._data_dep_dsts[data] = dep_source_id

  # if this atom is the target of a data dependency
  if atom._label in thread._data_dep_dsts:
    req = thread._data_dep_dsts[atom._label]
    s += "rd" + str(req)

  # if this atom is the source of an rmw
  if hasattr(atom, "rmw"):
    s += "m"
  # note: there is no need to also mark the target of an rmw, since it's
  # already unambiguous based on where the source is

  # save this hash for future reference
  thread._memo[atom._label] = s
  return s

def get_instance_hash(atoms):
  # there might be more than one thread with the same hash, so track hashes
  # and threads separately
  thread_hashes = {}
  threads_with_hash = {}

  # search all the atoms for ones labeled "Thread"
  for t in atoms.iteritems():
    if t[0][:7] == "Thread$":
      thread_hash = ""
      # iterate through the events in the thread, and add the event hash of
      # each to the thread's hash
      s = follow_edge(t[1], "start")
      while s is not None:
        a = atoms[s]
        thread_hash += event_hash_without_addr(t[1], a)
        s = follow_po_edge(atoms, a)
      thread_hashes[t[0]] = thread_hash
      threads_with_hash.setdefault(thread_hash, set()).add(t[0])

  # addrmap: map each address into a name sorted by first appearance in the
  # instance hash
  addrmap = {}

  # generate the instance hash, which is the alphabetical sort of the thread
  # hashes
  instance_hash = ""
  for th in sorted(threads_with_hash.keys()):
    for t in threads_with_hash[th]:
      # precede each new thread with "_T"
      instance_hash += "_T"
      # re-iterate through the events in the thread, but this time add the
      # event's address to the hash too
      s = follow_edge(atoms[t], "start")
      while s is not None:
        a = atoms[s]
        instance_hash += event_hash_without_addr(atoms[t], a)
        addr = follow_edge(a, "address")
        if addr is not None:
          addrmap.setdefault(atoms[addr], len(addrmap.keys()))
          instance_hash += "a" + str(addrmap[atoms[addr]])
        s = follow_po_edge(atoms, a)

  if instance_hash == "":
    raise Exception("Empty hash for instance %s" % str(atoms))
  return instance_hash

def parse(instance):
  global total, unique, last_message
  atoms = {}

  # Parse the Alloy XML dump

  # first, parse all the sigs in the instance
  for sig in instance.findall("sig"):
    sig_label = re.sub(".*/", "", sig.attrib["label"])
    # parse all the atoms which are members of this sig
    for atom in sig.findall("atom"):
      label = re.sub(".*/", "", atom.attrib["label"])
      atoms[label] = Atom(label, sig_label)

  # parse all the relations in the instance
  for field in instance.findall("field"):
    field_label = re.sub(".*/", "", field.attrib["label"])
    # parse each individual edge in the relation
    for tup in field.findall("tuple"):
      # parse the atoms in each edge.  there should be two: a source and a
      # destination
      tuple_atoms = []
      for atom in tup.findall("atom"):
        tuple_atoms.append(re.sub(".*/", "", atom.attrib["label"]))
      if len(tuple_atoms) == 2:
        src = tuple_atoms[0]
        dst = tuple_atoms[1]
        if hasattr(atoms[src], field_label):
          val = getattr(atoms[src], field_label)
        else:
          val = set()
        val.add(dst)
        setattr(atoms[src], field_label, val)
      else:
        raise Exception("illegal tuple arity")

  # get a hash of the parsed Alloy instance
  instance_hash = get_instance_hash(atoms)

  # check whether we've seen this instance before
  total += 1
  if instance_hash in instances:
    # print a status message occasionally
    if total - last_message >= 500:
      sys.stdout.write("         (%d/%d)\n" % (unique, total))
      last_message = total
  else:
    unique += 1
    last_message = total
    sys.stdout.write("New hash (%d/%d): %s\n" % (unique, total, instance_hash))
    sys.stdout.flush()
    instances[instance_hash] = atoms

def run():
  instance_text = ""
  for ln in sys.stdin:
    if ln == "": #EOF
      break

    # pre-parse the XML to search for individual commands
    if "<command" in ln:
      match = re.search("label=\"(.*)\"", ln)
      command = match.group(1).split(':')

    # pre-parse the XML to search for individual instances of the latest command
    if "<instance" in ln:
      instance_text = ""
    instance_text += ln
    if "</instance" in ln:
      # we've reached the end of an instance, so parse this instance
      parse(ET.fromstring(instance_text))

  # print out the final results
  sys.stdout.write("#,Filename,Command,Unique,Total\n")
  sys.stdout.write("Results,%s,%s,%d,%d\n" % (command[0], command[1], unique, total))

sys.stdout.write("# %s\n" % sys.argv)
run()

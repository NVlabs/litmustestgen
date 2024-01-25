// Automated Synthesis of Comprehensive Memory Model Litmus Test Suites
// Daniel Lustig, Andrew Wright, Alexandros Papakonstantinou, Olivier Giroux
// ASPLOS 2017
//
// Copyright (c) 2017, NVIDIA Corporation.  All rights reserved.
//
// This file is licensed under the BSD-3 license.  See LICENSE for details.

// Total Store Ordering (TSO)

////////////////////////////////////////////////////////////////////////////////
// =Perturbations=

abstract sig PTag {}

one sig RE extends PTag {} // Remove Event
one sig RD extends PTag {} // Remove Dependency (RMW)

fun no_p : PTag->univ { // no_p - constant for no perturbation
  (PTag->univ) - (PTag->univ)
}

////////////////////////////////////////////////////////////////////////////////
// =TSO memory model=

pred sc_per_loc[p: PTag->univ] {
  acyclic[rf_p[p] + co_p[p] + fr_p[p] + po_loc_p[p]]
}
pred rmw_atomicity[p: PTag->univ] {
  no (fr_p[p]).(co_p[p]) & rmw_p[p]
}
pred causality[p: PTag->univ] {
  acyclic[rfe_p[p] + co_p[p] + fr_p[p] + ppo_p[p] + fence_p[p]]
}

pred tso_p[p: PTag->univ] {
  sc_per_loc[p]
  rmw_atomicity[p]
  causality[p]
}

fun fence_p[p: PTag->univ] : MemoryEvent->MemoryEvent {
  ((MemoryEvent - p[RE]) <: ^po :> (Fence - p[RE])).(^po :> (MemoryEvent - p[RE]))
}
fun ppo_p[p: PTag->univ] : MemoryEvent->MemoryEvent {
  ((MemoryEvent - p[RE]) <: ^po :> (MemoryEvent - p[RE]))
  -
  ((Write - ((Read - p[RD]).rmw))->((Read - p[RD]) - Write.~rmw))
}

////////////////////////////////////////////////////////////////////////////////
// =Basic model of memory=

sig Address { }

sig Thread { start: one Event }

abstract sig Event { po: lone Event }

abstract sig MemoryEvent extends Event {
  address: one Address,
  dep: set MemoryEvent,
}
sig Read extends MemoryEvent { rmw: lone Write }
sig Write extends MemoryEvent { rf: set Read, co: set Write }

sig Fence extends Event {}

////////////////////////////////////////////////////////////////////////////////
// =Constraints on basic model of memory=

// All communication is via accesses to the same address
fact { com in address.~address }

// Program order is sane
fact { acyclic[po] }
fact { all e: Event | one t: Thread | t->e in start.*po }
fun po_loc : MemoryEvent->MemoryEvent { ^po & address.~address }

// Dependencies go from Reads to Reads or Writes
fact { dep in Read <: ^po }

// co is a per-address total order
fact { all a: Address | total[co, a.~address :> Write] }

// Each read sources from at most one write
// (could be zero if sourcing from the initial condition)
fact { rf.~rf in iden }
// fr is defined in the standard way
fun fr : Read->Write {
  ~rf.co
  +
  // also include reads that read from the initial state
  ((Read - (Write.rf)) <: (address.~address) :> Write)
}

// RMW pairs are sane and overlap with dep
fact { rmw in po & dep & address.~address }

//////////////////////////////////////////////////////////////////////////////////////////////////////////////
// =Model of memory, under perturbation=

// po is not transitive
fun po_t[p: PTag->univ] : Event->Event { (Event - p[RE]) <: ^po :> (Event - p[RE]) }
fun po_p[p: PTag->univ] : Event->Event { po_t[p] - (po_t[p]).(po_t[p]) }

// po_loc is already transitive
fun po_loc_p[p: PTag->univ] : MemoryEvent->MemoryEvent { (MemoryEvent - p[RE]) <: po_loc :> (MemoryEvent - p[RE]) }

// dep is not transitive
fun dep_p[p: PTag->univ] : MemoryEvent->MemoryEvent {
  (Read - p[RE] - p[RD]) <: *(dep :> p[RE]).dep :> (MemoryEvent - p[RE])
}

fun rf_p[p: PTag->univ] : Write->Read { (Write - p[RE]) <: rf :> (Read - p[RE]) }
fun co_p[p: PTag->univ] : Write->Write { (Write - p[RE]) <: co :> (Write - p[RE]) }
//fun fr_p[p: PTag->univ] : Read->Write { (Read - p[RE]) <: fr :> (Write - p[RE]) }
fun fr_p[p: PTag->univ] : Read->Write {
  ( ~(rf_p[p]).^(co_p[p]) )
  +
  ( (Read-(Write.rf)-p[RE]) <: address.~address :> (Write - p[RE]) )
}
fun rmw_p[p: PTag->univ] : Read->Write { (Read - p[RE] - p[RD]) <: rmw :> (Write - p[RE]) }

////////////////////////////////////////////////////////////////////////////////
// =Shortcuts=

fun same_thread [rel: Event->Event] : Event->Event {
  rel & ( iden + ^po + ~^po )
}

fun com[] : MemoryEvent->MemoryEvent { rf + fr + co }
fun rfi[] : MemoryEvent->MemoryEvent { same_thread[rf] }
fun rfe[] : MemoryEvent->MemoryEvent { rf - rfi[] }
fun fri[] : MemoryEvent->MemoryEvent { same_thread[fr] }
fun fre[] : MemoryEvent->MemoryEvent { fr - fri }
fun coi[] : MemoryEvent->MemoryEvent { same_thread[co] }
fun coe[] : MemoryEvent->MemoryEvent { co - coi }

fun com_p[p: PTag->univ] : MemoryEvent->MemoryEvent { rf_p[p] + fr_p[p] + co_p[p] }
fun rfi_p[p: PTag->univ] : MemoryEvent->MemoryEvent { same_thread[rf_p[p]] }
fun rfe_p[p: PTag->univ] : MemoryEvent->MemoryEvent { rf_p[p] - rfi_p[p] }
fun fri_p[p: PTag->univ] : MemoryEvent->MemoryEvent { same_thread[fr_p[p]] }
fun fre_p[p: PTag->univ] : MemoryEvent->MemoryEvent { fr_p[p] - fri_p[p] }
fun coi_p[p: PTag->univ] : MemoryEvent->MemoryEvent { same_thread[co_p[p]] }
fun coe_p[p: PTag->univ] : MemoryEvent->MemoryEvent { co_p[p] - coi_p[p] }

////////////////////////////////////////////////////////////////////////////////
// =Alloy helpers=

pred irreflexive[rel: Event->Event]        { no iden & rel }
pred acyclic[rel: Event->Event]            { irreflexive[^rel] }
pred total[rel: Event->Event, bag: Event] {
  all disj e, e2: bag | e->e2 in rel + ~rel
  acyclic[rel]
}

//////////////////////////////////////////////////////////////////////////////////////////////////////////////
// =Constraints on the search space=

fact {
  all a: Address | some (a.~address) :> Write
}

//////////////////////////////////////////////////////////////////////////////////////////////////////////////
// =Perturbation auxiliaries=

let interesting_not_axiom[axiom] {
  not axiom[no_p]

  // All events must be relevant and minimal
  all e: Event | tso_p[RE->(e + e.rmw + e.~rmw)]
  all e: Read | tso_p[RD->e] or no e.dep
}

////////////////////////////////////////////////////////////////////////////////

run sc_per_loc {
  interesting_not_axiom[sc_per_loc]
} for 4

run rmw_atomicity {
  interesting_not_axiom[rmw_atomicity]
} for 4

run causality {
  interesting_not_axiom[causality]
} for 4

run union {
  interesting_not_axiom[sc_per_loc]
  or
  interesting_not_axiom[rmw_atomicity]
  or
  interesting_not_axiom[causality]
} for 4

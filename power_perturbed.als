// Automated Synthesis of Comprehensive Memory Model Litmus Test Suites
// Daniel Lustig, Andrew Wright, Alexandros Papakonstantinou, Olivier Giroux
// ASPLOS 2017
//
// Copyright (c) 2017, NVIDIA Corporation.  All rights reserved.
//
// This file is licensed under the BSD-3 license.  See LICENSE for details.

// Based on a model from Herding Cats [Alglave et al., TOPLAS 2014]

//////////////////////////////////////////////////////////////////////////////////////////////////////////////
// =Perturbations=

abstract sig PTag {} // Perturbation Tag
one sig RE extends PTag {} // Remove Event
one sig RD extends PTag {} // Remove Dep
one sig DFSC extends PTag {} // Demote Fence (SC for compatibility with the canonicalizer)

fun no_p : PTag->univ { // no_p - constant for no perturbation
  (PTag->univ) - (PTag->univ)
}

////////////////////////////////////////////////////////////////////////////////
// =Power memory model=

pred sc_per_loc_p[p: PTag->univ] {
  acyclic[po_loc_p[p] + (com_p[p])]
}
pred no_thin_air_p[p: PTag->univ] {
  acyclic[hb_p[p]]
}
pred observation_p[p: PTag->univ] {
  irreflexive[fre_p[p].(prop_p[p]).*(hb_p[p])]
}
pred propagation_p[p: PTag->univ] {
  acyclic[co_p[p] + prop_p[p]]
}
pred power_p[p: PTag->univ] {
  sc_per_loc_p[p]
  no_thin_air_p[p]
  observation_p[p]
  propagation_p[p]
}

fun cfence_p[p: PTag->univ] : Event->Event {
  (^(po_p[p]) :> CtrlFence).^(po_p[p])
  +
  (^(po_p[p]) :> (lwsync & p[DFSC])).^(po_p[p])
}
fun lwfence_p[p: PTag->univ] : Event->Event {
  ((^(po_p[p]) :> (lwsync - p[DFSC])).^(po_p[p]))
  +
  ((^(po_p[p]) :> (sync & p[DFSC])).^(po_p[p]))
  -
  (^(po_p[p]) & Write->Read)
}
fun ffence_p[p: PTag->univ] : Event->Event {
  (^(po_p[p]) :> (sync - p[DFSC])).^(po_p[p])
}
fun fences_p[p: PTag->univ] : Event->Event {
  lwfence_p[p] + ffence_p[p]
} // not cfence

fun A_cumul_p[p: PTag->univ] : Event->Event {
  (rfe_p[p]).(fences_p[p])
}
fun prop_base_p[p: PTag->univ] : Event->Event {
  (fences_p[p] + A_cumul_p[p]).*(hb_p[p])
}
fun prop_p[p: PTag->univ] : Event->Event {
  (prop_base_p[p] & Write->Write)
  +
  (*(com_p[p]).*(prop_base_p[p]).(ffence_p[p]).*(hb_p[p]))
}

fun rdw_p[p: PTag->univ] : Event->Event { po_loc_p[p] & (fre_p[p].(rfe_p[p])) }
fun detour_p[p: PTag->univ] : Event->Event { po_loc_p[p] & (coe.(rfe_p[p])) }

fun ii0_p[p: PTag->univ] : Event->Event { addr_p[p] + data_p[p] + rdw_p[p] + rfi_p[p] }
fun ci0_p[p: PTag->univ] : Event->Event { ctrl_p[p].(cfence_p[p]) + detour_p[p] }
fun ic0_p[p: PTag->univ] : Event->Event { iden - iden }
fun cc0_p[p: PTag->univ] : Event->Event {
  addr_p[p] + data_p[p] + po_loc_p[p] + ctrl_p[p] + (addr_p[p].^(po_p[p]))
}
fun ii1_p[p: PTag->univ] : Event->Event {
  ii0_p[p] + (ci0_p[p]) + ((ic0_p[p]).(ci0_p[p])) + ((ii0_p[p]).(ii0_p[p]))
}
fun ci1_p[p: PTag->univ] : Event->Event {
  ci0_p[p] + ((ci0_p[p]).(ii0_p[p])) + ((cc0_p[p]).(ci0_p[p]))
}
fun ic1_p[p: PTag->univ] : Event->Event {
  ic0_p[p] + (ii0_p[p]) + (cc0_p[p]) + ((ic0_p[p]).(cc0_p[p])) + ((ii0_p[p]).(ic0_p[p]))
}
fun cc1_p[p: PTag->univ] : Event->Event {
  cc0_p[p] + (ci0_p[p]) + ((ci0_p[p]).(ic0_p[p])) + ((cc0_p[p]).(cc0_p[p]))
}
fun ii2_p[p: PTag->univ] : Event->Event {
  ii1_p[p] + (ci1_p[p]) + ((ic1_p[p]).(ci1_p[p])) + ((ii1_p[p]).(ii1_p[p]))
}
fun ci2_p[p: PTag->univ] : Event->Event {
  ci1_p[p] + ((ci1_p[p]).(ii1_p[p])) + ((cc1_p[p]).(ci1_p[p]))
}
fun ic2_p[p: PTag->univ] : Event->Event {
  ic1_p[p] + (ii1_p[p]) + (cc1_p[p]) + ((ic1_p[p]).(cc1_p[p])) + ((ii1_p[p]).(ic1_p[p]))
}
fun cc2_p[p: PTag->univ] : Event->Event {
  cc1_p[p] + (ci1_p[p]) + ((ci1_p[p]).(ic1_p[p])) + ((cc1_p[p]).(cc1_p[p]))
}
fun ii_p[p: PTag->univ] : Event->Event {
  ii2_p[p] + (ci2_p[p]) + ((ic2_p[p]).(ci2_p[p])) + ((ii2_p[p]).(ii2_p[p]))
}
fun ci_p[p: PTag->univ] : Event->Event {
  ci2_p[p] + ((ci2_p[p]).(ii2_p[p])) + ((cc2_p[p]).(ci2_p[p]))
}
fun ic_p[p: PTag->univ] : Event->Event {
  ic2_p[p] + (ii2_p[p]) + (cc2_p[p]) + ((ic2_p[p]).(cc2_p[p])) + ((ii2_p[p]).(ic2_p[p]))
}
fun cc_p[p: PTag->univ] : Event->Event {
  cc2_p[p] + (ci2_p[p]) + ((ci2_p[p]).(ic2_p[p])) + ((cc2_p[p]).(cc2_p[p]))
}

fun ppo_p[p: PTag->univ] : Event->Event {
  (ii_p[p] & ^(po_p[p]) & Read->Read)
  +
  (ic_p[p] & ^(po_p[p]) & Read->Write)
}

fun hb_p[p: PTag->univ] : Event->Event {
  ppo_p[p] + fences_p[p] + rfe_p[p]
}

//////////////////////////////////////////////////////////////////////////////////////////////////////////////
// =Basic model of memory=

sig Address { }

sig Thread { start: one Event }

abstract sig Event {
  po: lone Event, 
}

abstract sig MemoryEvent extends Event {
  address: one Address,
}
sig Read extends MemoryEvent {
  rmw: lone Write,
  addr: set Event,
  ctrl: set Event,
  data: set Event,
}
fun dep : Read->Event { addr + ctrl + data }
sig Write extends MemoryEvent {
  rf: set Read,
  co: set Write
}

abstract sig Fence extends Event { }
sig CtrlFence extends Fence {}
sig lwsync extends Fence {}
sig sync extends Fence {}

//address
fact { co + rf + fr in address.~address }

//po
fact { acyclic[po] }
fact { all e: Event | one t: Thread | t->e in start.*po }
fun po_loc : Event->Event { ^po & address.~address }

//writes
fact { all a: Address | total[co, a.~address :> Write] }

//reads
fact { rf.~rf in iden }
fun fr : Read->Write {
  ~rf.co
  +
  // also include reads that read from the initial state
  ((Read - (Write.rf)) <: (address.~address) :> Write)
}

//dep
fact { dep in ^po }

//rmws
fact { rmw in po & dep & address.~address }

//////////////////////////////////////////////////////////////////////////////////////////////////////////////
// =Model of memory, under perturbation=

// po is not transitive
fun po_t[p: PTag->univ] : Event->Event { (Event - p[RE]) <: ^po :> (Event - p[RE]) }
fun po_p[p: PTag->univ] : Event->Event { po_t[p] - (po_t[p]).(po_t[p]) }

// po_loc is already transitive
fun po_loc_p[p: PTag->univ] : MemoryEvent->MemoryEvent { (MemoryEvent - p[RE]) <: ^po_loc :> (MemoryEvent - p[RE]) }

// no need for rmw_p, since rmws are removed in pairs FIXME
fun rf_p[p: PTag->univ] : Write->Read { (Write - p[RE]) <: rf :> (Read - p[RE]) }
fun co_p[p: PTag->univ] : Write->Write { (Write - p[RE]) <: co :> (Write - p[RE]) }
fun fr_p[p: PTag->univ] : Read->Write { (Read - p[RE]) <: fr :> (Write - p[RE]) }
//fun fr_p[p: PTag->univ] : Read->Write {
//  ( ~(rf_p[p]).^(co_p[p]) )
//  +
//  ( (Read-(Write.rf)-p[RE]) <: address.~address :> (Write - p[RE]) )
//  //((Read - p[RE])->(Write - p[RE]) & address.~address) - (~(rf_p[p]).*(co_p[p]))
//}

fun addr_p[p: PTag->univ] : Event->Event {
  (Event - p[RE+RD]) <: addr :> (Event - p[RE])
}
fun ctrl_p[p: PTag->univ] : Event->Event {
  (Event - p[RE+RD]) <: ctrl :> (Event - p[RE])
  +
  ((Event & p[RD]) - p[RE]) <: data :> (Event - p[RE])
}
fun data_p[p: PTag->univ] : Event->Event {
  (Event - p[RE+RD]) <: data :> (Event - p[RE])
  +
  ((Event & p[RD]) - p[RE]) <: addr :> (Event - p[RE])
}

////////////////////////////////////////////////////////////////////////////////
// =Shortcuts=

fun same_thread [rel: Event->Event] : Event->Event {
  rel & (iden + ^po + ~^po)
}

fun com : MemoryEvent->MemoryEvent { rf + fr + co }
fun rfi : MemoryEvent->MemoryEvent { same_thread[rf] }
fun rfe : MemoryEvent->MemoryEvent { rf - rfi }
fun fri : MemoryEvent->MemoryEvent { same_thread[fr] }
fun fre : MemoryEvent->MemoryEvent { fr - fri }
fun coi : MemoryEvent->MemoryEvent { same_thread[co] }
fun coe : MemoryEvent->MemoryEvent { co - coi }

fun com_p[p: PTag->univ] : MemoryEvent->MemoryEvent { rf_p[p] + fr_p[p] + co_p[p] }
fun rfi_p[p: PTag->univ] : MemoryEvent->MemoryEvent { same_thread[rf_p[p]] }
fun rfe_p[p: PTag->univ] : MemoryEvent->MemoryEvent { rf_p[p] - rfi_p[p] }
fun fri_p[p: PTag->univ] : MemoryEvent->MemoryEvent { same_thread[fr_p[p]] }
fun fre_p[p: PTag->univ] : MemoryEvent->MemoryEvent { fr_p[p] - fri_p[p] }
fun coi_p[p: PTag->univ] : MemoryEvent->MemoryEvent { same_thread[co_p[p]] }
fun coe_p[p: PTag->univ] : MemoryEvent->MemoryEvent { co_p[p] - coi_p[p] }

//////////////////////////////////////////////////////////////////////////////////////////////////////////////
// =Alloy helpers=

pred irreflexive[rel: Event->Event]        { no iden & rel }
pred acyclic[rel: Event->Event]            { irreflexive[^rel] }
pred total[rel: Event->Event, bag: Event] {
  all disj e, e': bag | e->e' in rel + ~rel
  acyclic[rel]
}

////////////////////////////////////////////////////////////////////////////////
// =Perturbation auxiliaries=

let interesting[axiom] {
  not axiom[no_p]
  all e: Event | power_p[RE->e]
  all f: lwsync+sync | power_p[DFSC->f]
  all r: Read | no r.dep or power_p[RD->r]
}

//////////////////////////////////////////////////////////////////////////////////////////////////////////////
// =Constraints on the search space=

fact {
  all a: Address | some (a.~address) :> Write
}

////////////////////////////////////////////////////////////////////////////////

pred sc_per_loc {
  interesting[sc_per_loc_p]
}
run sc_per_loc for 3

pred no_thin_air {
  interesting[no_thin_air_p]
}
run no_thin_air for 3

pred observation {
  interesting[observation_p]
}
run observation for 3

pred propagation {
  interesting[propagation_p]
}
run propagation for 3

pred union {
  interesting[sc_per_loc_p]
  or
  interesting[no_thin_air_p]
  or
  interesting[observation_p]
  or
  interesting[propagation_p]
}
run union for 3

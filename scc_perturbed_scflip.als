// Automated Synthesis of Comprehensive Memory Model Litmus Test Suites
// Daniel Lustig, Andrew Wright, Alexandros Papakonstantinou, Olivier Giroux
// ASPLOS 2017
//
// Copyright (c) 2017, NVIDIA Corporation.  All rights reserved.
//
// This file is licensed under the BSD-3 license.  See LICENSE for details.

// Streamlined Causal Consistency (SCC) Model

////////////////////////////////////////////////////////////////////////////////
// =Perturbations=

abstract sig PTag {}

one sig RE extends PTag {} // Remove Event
one sig DRA extends PTag {} // Demote Release Acquire
one sig DFSC extends PTag {} // Demote FenceSC
one sig RD extends PTag {} // Remove Dependency

fun no_p : PTag->univ { // no_p - constant for no perturbation
  (PTag->univ) - (PTag->univ)
}

////////////////////////////////////////////////////////////////////////////////
// =SCC memory model=

pred scc_p[p: PTag->univ] {
  sc_per_loc_p[p]
  no_thin_air_p[p]
  rmw_atomicity_p[p]
  causality_p[p]
}

// HACK!!! see the paper
fact { lone sc }
pred scc_scflip[p: PTag->univ] {
  sc_per_loc_p[p]
  no_thin_air_p[p]
  rmw_atomicity_p[p]
  causality_scflip_p[p]
}

pred sc_per_loc_p[p: PTag->univ] {
  acyclic[com_p[p] + po_loc_p[p]]
}
pred no_thin_air_p[p: PTag->univ] {
  acyclic[rf_p[p] + dep_p[p]]
}
pred rmw_atomicity_p[p: PTag->univ] {
  no (fr_p[p]).(co_p[p]) & rmw_p[p]
}
pred causality_p[p: PTag->univ] {
  irreflexive[*(com_p[p]).^(cause_p[p])]
}

// HACK!!! see the paper
pred causality_scflip_p[p: PTag->univ] {
  irreflexive[*(com_p[p]).^(cause_p[p])]
  or
  irreflexive[*(com_p[p]).^(cause_scflip_p[p])]
}

fun prefix_p[p: PTag->univ] : Event->Event {
  iden + ((Fence - p[RE]) <: po_p[p]) + ((Release - p[RE] - p[DRA]) <: po_loc_p[p])
}
fun suffix_p[p: PTag->univ] : Event->Event {
  iden + (po_p[p] :> (Fence - p[RE])) + (po_loc_p[p] :> (Acquire - p[RE] - p[DRA]))
}
fun observation_p[p: PTag->univ] : Event->Event {
  rf_p[p] + rmw_p[p]
}
fun Releasers_p[p: PTag->univ] : Event {
  (Release - p[RE] - p[DRA]) + (Fence - p[RE])
}
fun Acquirers_p[p: PTag->univ] : Event {
  (Acquire - p[RE] - p[DRA]) + (Fence - p[RE])
}
fun sync_p[p: PTag->univ] : Event->Event {
  Releasers_p[p] <: (prefix_p[p]).^(observation_p[p]).(suffix_p[p]) :> Acquirers_p[p]
}
fun cause_p[p: PTag->univ] : MemoryEvent->MemoryEvent {
  *(po_p[p]).(sc_p[p] + sync_p[p]).*(po_p[p])
}
fun cause_scflip_p[p: PTag->univ] : MemoryEvent->MemoryEvent {
  *(po_p[p]).(~(sc_p[p]) + sync_p[p]).*(po_p[p])
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
sig Acquire extends Read { }
sig Write extends MemoryEvent { rf: set Read, co: set Write }
sig Release extends Write { }

abstract sig Fence extends Event {}
sig FenceAll extends Fence { }
sig FenceSC extends FenceAll {
  sc: set FenceSC
}

////////////////////////////////////////////////////////////////////////////////
// =Constraints on basic model of memory=

// All communication is via accesses to the same address
fact { com in address.~address }

// Program order is sane
fact { acyclic[po] }
fact { all e: Event | one t: Thread | t->e in start.*po }
fun po_loc : Event->Event { ^po & address.~address }

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

// sc is a total order on FenceSCs
fact { total[sc, FenceSC] }

//////////////////////////////////////////////////////////////////////////////////////////////////////////////
// =Model of memory, under perturbation=

// po is not transitive
fun po_t[p: PTag->univ] : Event->Event { (Event - p[RE]) <: ^po :> (Event - p[RE]) }
fun po_p[p: PTag->univ] : Event->Event { po_t[p] - (po_t[p]).(po_t[p]) }

// po_loc is already transitive
fun po_loc_p[p: PTag->univ] : MemoryEvent->MemoryEvent { (MemoryEvent - p[RE]) <: ^po_loc :> (MemoryEvent - p[RE]) }

// dep is not transitive
fun dep_p[p: PTag->univ] : MemoryEvent->MemoryEvent {
  (Read - p[RE] - p[RD]) <: *(dep :> p[RE]).dep :> (MemoryEvent - p[RE])
}

fun rf_p[p: PTag->univ] : Write->Read { (Write - p[RE]) <: rf :> (Read - p[RE]) }
fun co_p[p: PTag->univ] : Write->Write { (Write - p[RE]) <: co :> (Write - p[RE]) }
fun fr_p[p: PTag->univ] : Read->Write { (Read - p[RE]) <: fr :> (Write - p[RE]) }
//fun fr_p[p: PTag->univ] : Read->Write {
//  ( ~(rf_p[p]).^(co_p[p]) )
//  +
//  ( (Read-(Write.rf)-p[RE]) <: address.~address :> (Write - p[RE]) )
//  //((Read - p[RE])->(Write - p[RE]) & address.~address) - (~(rf_p[p]).*(co_p[p]))
//}
fun rmw_p[p: PTag->univ] : Read->Write { (Read - p[RE] - p[RD]) <: rmw :> (Write - p[RE]) }

// sc is not transitive
fun sc_t[p: PTag->univ] : Event->Event { (Event - p[RE] - p[DFSC]) <: ^sc :> (Event - p[RE] - p[DFSC]) }
fun sc_p[p: PTag->univ] : Event->Event { sc_t[p] - (sc_t[p]).(sc_t[p]) }

////////////////////////////////////////////////////////////////////////////////
// =Shortcuts=

fun same_thread [rel: Event->Event] : Event->Event {
  rel & ( iden + ^po + ~^po )
}

fun com : MemoryEvent->MemoryEvent { rf + fr + co }
fun rfi : MemoryEvent->MemoryEvent { same_thread[rf] }
fun rfe : MemoryEvent->MemoryEvent { rf - rfi[] }
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

////////////////////////////////////////////////////////////////////////////////
// =Alloy helpers=

pred irreflexive[rel: Event->Event]        { no iden & rel }
pred acyclic[rel: Event->Event]            { irreflexive[^rel] }
pred total[rel: Event->Event, bag: Event] {
  all disj e, e': bag | e->e' in rel + ~rel
  acyclic[rel]
}

//////////////////////////////////////////////////////////////////////////////////////////////////////////////
// =Perturbation auxiliaries=

let interesting_not_axiom[axiom] {
  not axiom[no_p]

  // All events must be relevant and minimal
  all e: Event | scc_p[RE->(e + e.rmw + e.~rmw)]
  all e: Release+Acquire | scc_p[DRA->e]
  all f: FenceSC | scc_p[DFSC->f]
  all r: Read | scc_p[RD->r] or no r.dep
}

let interesting_not_axiom_scflip[axiom] {
  not axiom[no_p]

  // All events must be relevant and minimal
  all e: Event | scc_scflip[RE->(e + e.rmw + e.~rmw)]
  all e: Release+Acquire | scc_scflip[DRA->e]
  all f: FenceSC | scc_scflip[DFSC->f]
  all r: Read | scc_scflip[RD->r] or no r.dep
}

//////////////////////////////////////////////////////////////////////////////////////////////////////////////
// =Constraints on the search space=

fact {
  all a: Address | some (a.~address) :> Write
}
fact {
  irreflexive[^po.sc]
}

////////////////////////////////////////////////////////////////////////////////

run sc_per_loc {
  interesting_not_axiom[sc_per_loc_p]
} for 3

run no_thin_air {
  interesting_not_axiom[no_thin_air_p]
} for 3

run rmw_atomicity {
  interesting_not_axiom[rmw_atomicity_p]
} for 3

run causality {
  interesting_not_axiom[causality_p]
} for 3

run causality_scflip {
  interesting_not_axiom_scflip[causality_scflip_p]
} for 3 but 2 FenceSC

run union {
  interesting_not_axiom[sc_per_loc_p]
  or
  interesting_not_axiom[no_thin_air_p]
  or
  interesting_not_axiom[rmw_atomicity_p]
  or
  interesting_not_axiom[causality_p]
} for 3

run union_scflip {
  interesting_not_axiom[sc_per_loc_p]
  or
  interesting_not_axiom[no_thin_air_p]
  or
  interesting_not_axiom[rmw_atomicity_p]
  or
  interesting_not_axiom_scflip[causality_scflip_p]
} for 3 but 2 FenceSC

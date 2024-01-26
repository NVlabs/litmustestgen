// Automated Synthesis of Comprehensive Memory Model Litmus Test Suites
// Daniel Lustig, Andrew Wright, Alexandros Papakonstantinou, Olivier Giroux
// ASPLOS 2017
//
// Copyright (c) 2017, NVIDIA Corporation.  All rights reserved.
//
// This file is licensed under the BSD-3 license.  See LICENSE for details.

// C11/C++11, based on a model from Batty et al. [POPL 2016]

////////////////////////////////////////////////////////////////////////////////
// =Perturbations=

abstract sig PTag {}
one sig RE extends PTag {}
one sig LS extends PTag {}
one sig DR extends PTag {}
one sig DA extends PTag {}

fun no_p : PTag->univ { // no_p - constant for no perturbation
  (PTag->univ) - (PTag->univ)
}

////////////////////////////////////////////////////////////////////////////////
// =C11 memory model=

pred C11_p[p: PTag->univ] {
  DRF_p[no_p] // <-- !!!
  Hb_p[p]
  Coh_p[p]
  Rf_p[p]
  NaRf_p[p]
  Rmw_p[p]
  Ssimp_p[p]
}

pred Hb_p[p: PTag->univ] { irreflexive[hb_p[p]] }
pred Coh_p[p: PTag->univ] {
  irreflexive[optional[~(rf_p[p])].(mo_p[p]).(optional[rf_p[p]]).(hb_p[p])]
}
pred Rf_p[p: PTag->univ] { irreflexive[(rf_p[p]).(hb_p[p])] }
pred NaRf_p[p: PTag->univ] {
  no ((rf_p[p]).(ident[NA - p[RE]])) - vis_p[p]
}
pred Rmw_p[p: PTag->univ] {
  irreflexive[rf_p[p] + ((mo_p[p]).(mo_p[p]).~(rf_p[p])) + ((mo_p[p]).(rf_p[p]))]
}

pred Com_p[p: PTag->univ] { irreflexive[*(rf_p[p] + mo_p[p] + fr_p[p]).(hb_p[p])] }
pred Ssimp_p[p: PTag->univ] {
  acyclic[
    (allpairs[MemoryOrderSeqCst.(ord_p[p])] - iden)
    &
    (optional[Fsb_p[p]].(hb_p[p] + fr_p[p] + mo_p[p]).(optional[sbF_p[p]]))
  ]
}

pred DRF_p[p: PTag->univ] {
  no dr_p[p]
  // Not in the model, but in Batty's thesis, section 3.1.3
  Reads_p[p] in Writes_p[p].(rf_p[p]) // indeterminate reads
  ((address.~address) & ^(~(sb_p[p]) + sb_p[p])) - iden in sb_p[p] + ~(sb_p[p]) // unsequenced races
}

//////////////////////////////////////////////////////////////////////////////////////////////////////////////
// =Model of memory=

sig Address { }

sig Thread { start: one Event }
fact { start.~start in iden }
fact { Event = Thread.start.*sb }
fact { no start.~sb }

abstract sig MemoryOrder {}
one sig MemoryOrderNonAtomic extends MemoryOrder {}
one sig MemoryOrderRelaxed   extends MemoryOrder {}
one sig MemoryOrderAcquire   extends MemoryOrder {}
one sig MemoryOrderRelease   extends MemoryOrder {}
one sig MemoryOrderAcqRel    extends MemoryOrder {}
one sig MemoryOrderSeqCst    extends MemoryOrder {}

fun A : Event { Event - MemoryOrderNonAtomic.ord }
fun NA : set Event { MemoryOrderNonAtomic.ord }
fun RLX : set Event { MemoryOrderRelaxed.ord }
fun ACQ : set Event { MemoryOrderAcquire.ord }
fun REL : set Event { MemoryOrderRelease.ord }
fun AR : set Event { MemoryOrderAcqRel.ord }
fun SC : set Event { MemoryOrderSeqCst.ord }

fun acq : set Event { ACQ + AR + SC - Write }
fun rel : set Event { REL + AR + SC - Read }

fact WriteMO {
  all w: Write | w.memory_order in
  MemoryOrderNonAtomic + MemoryOrderRelaxed +
  MemoryOrderRelease + MemoryOrderSeqCst
}
fact ReadMO {
  Read.memory_order in
  MemoryOrderNonAtomic + MemoryOrderRelaxed +
  MemoryOrderAcquire + MemoryOrderSeqCst
}
fact RMWMO {
  RMW.memory_order in
  MemoryOrderRelaxed + MemoryOrderRelease + MemoryOrderAcquire +
  MemoryOrderAcqRel + MemoryOrderSeqCst
}
fact {
  Fence.memory_order in
  MemoryOrderRelease + MemoryOrderAcquire + MemoryOrderAcqRel + MemoryOrderSeqCst
}

abstract sig Event {
  sb: set Event,
  memory_order: one MemoryOrder,
  sc: set Event,
}
fun ord : MemoryOrder->Event { ~memory_order }
abstract sig MemoryEvent extends Event {
  address : one Address,
  rf: set Event,
  mo: set Event,
}
fact rf_wr { rf in Writes->Reads }
fact mo_writes { mo in Writes->Writes }
sig Write extends MemoryEvent {}
sig Read extends MemoryEvent {}
sig RMW extends MemoryEvent {}
sig Fence extends Event {}
fun Reads : set Event { Read + RMW }
fun Writes : set Event { Write + RMW }

////////////////////////////////////////////////////////////////////////////////
// =Constraints on basic model of memory=

// com
fun loc : Event->Event { MemoryEvent->MemoryEvent & address.~address }
fact { all r : Reads | lone r.~rf }
fun fr : Read->Write {
  ~rf.mo
  +
  ((Reads - Writes.rf)->Writes & loc)
}
fact com_loc { rf + mo + fr in loc }

// sb
fact { irreflexive[sb] }
fact { transitive[sb] }
fact { all e: Event | one t: Thread | t->e in start.*sb }
fun thd : Event->Event { ^(sb + ~sb) }

// reads
fact { rf.~rf in iden }

// writes
fact { all a: Address | total[mo, a.~address :> (Writes & A)] }
//fact { no NA <: address.~address :> A }

// sc
fact { total[sc, SC] }
fact { sc in allpairs[SC] }

//////////////////////////////////////////////////////////////////////////////////////////////////////////////
// =Model of memory, under perturbation=

fun DR_step : MemoryOrder->MemoryOrder {
  MemoryOrderAcqRel->MemoryOrderSeqCst +
  MemoryOrderRelease->MemoryOrderAcqRel +
  MemoryOrderRelaxed->MemoryOrderAcquire + // should still work here
  MemoryOrderRelaxed->MemoryOrderRelease
}

fun DA_step : MemoryOrder->MemoryOrder {
  MemoryOrderAcqRel->MemoryOrderSeqCst +
  MemoryOrderAcquire->MemoryOrderAcqRel +
  MemoryOrderRelaxed->MemoryOrderRelease + // should still work here
  MemoryOrderRelaxed->MemoryOrderAcquire
}

fun ord_p[p: PTag->univ] : MemoryOrder->Event {
  ord :> (Event - p[RE+DR+DA])
  +
  DR_step.ord :> ((Event & p[DR]) - p[RE])
  +
  DA_step.ord :> ((Event & p[DA]) - p[RE])
}

fun sb_p[p: PTag->univ] : Event->Event {
  (Event - p[RE]) <: sb :> (Event - p[RE])
}

fun sc_p[p: PTag->univ] : Event->Event {
  (Event - p[RE+DR+DA]) <: sc :> (Event - p[RE+DR+DA])
}

fun rf_p[p: PTag->univ] : Event->Event {
  (Event - p[RE]) <: rf :> (Event - p[RE])
}

fun mo_p[p: PTag->univ] : Event->Event {
  (Event - p[RE]) <: mo :> (Event - p[RE])
}

fun fr_p[p: PTag->univ] : Event->Event {
  (Event - p[RE]) <: fr :> (Event - p[RE])
}

fun Writes_p[p: PTag->univ] : Event {
  Writes - p[RE]
}

fun Reads_p[p: PTag->univ] : Event {
  Reads - p[RE]
}

fun thd_p[p: PTag->univ] : Event->Event {
  (Event - p[RE]) <: thd :> (Event - p[RE])
}

fun acq_p[p: PTag->univ] : set Event {
  (MemoryOrderAcquire.(ord_p[p])) +
  (MemoryOrderAcqRel.(ord_p[p])) +
  (MemoryOrderSeqCst.(ord_p[p]) & (Reads + Fence))
  // + (F & con) // ignoring consume
}
fun rel_p[p: PTag->univ] : set Event {
  (MemoryOrderRelease.(ord_p[p])) +
  (MemoryOrderAcqRel.(ord_p[p])) +
  (MemoryOrderSeqCst.(ord_p[p]) & (Writes + Fence))
  // + (F & con)? // ignoring consume
}
fun Fsb_p[p: PTag->univ] : Event->Event { ident[Fence].(sb_p[p]) }
fun sbF_p[p: PTag->univ] : Event->Event { (sb_p[p]).(ident[Fence]) }
fun rs_prime_p[p: PTag->univ] : Event->Event {
  thd_p[p] + (((Event - p[RE])->(Event - p[RE])).(ident[RMW]))
}
fun rs_p[p: PTag->univ] : Event->Event {
  (mo_p[p]) & (rs_prime_p[p]) - (((mo_p[p]) - (rs_prime_p[p])).(mo_p[p]))
}
fun sw_p[p: PTag->univ] : Event->Event {
  (
    (ident[rel_p[p]]).(optional[Fsb_p[p]]).(ident[Writes])
    .(optional[rs_p[p]]).(rf_p[p]).(ident[Reads])
    .(optional[sbF_p[p]]).(ident[acq_p[p]])
  ) - thd_p[p]
}
fun ithbr_p[p: PTag->univ] : Event->Event { sw_p[p] + (sw_p[p]).(sb_p[p]) }
fun ithb_p[p: PTag->univ] : Event->Event {
  ^(ithbr_p[p] + (sb_p[p]).(ithbr_p[p]))
}
fun hb_p[p: PTag->univ] : Event->Event {
  ^((sb_p[p]) + ithb_p[p])
}
fun hbl_p[p: PTag->univ] : Event->Event { hb_p[p] & loc }
fun vis_p[p: PTag->univ] : Event->Event {
  (ident[Writes].(hbl_p[p]).(ident[Reads]))
  -
  ((hbl_p[p]).(ident[Writes]).(hbl_p[p]))
}
fun cnf_p[p: PTag->univ] : Event->Event {
  (((MemoryEvent - p[RE])->(MemoryEvent - p[RE])) & loc)
}
fun dr_p[p: PTag->univ] : Event->Event {
  cnf_p[p] - hb_p[p] - ~(hb_p[p]) - allpairs[Event - NA - p[RE]] - thd_p[p]
}

//////////////////////////////////////////////////////////////////////////////////////////////////////////////
// =Alloy helpers=

fun allpairs[e: univ] : univ->univ        { e->e }
fun ident[e: univ] : univ->univ           { iden & e->e }
fun optional[f: univ->univ] : univ->univ  { iden + f }
pred transitive[rel: Event->Event]        { rel = ^rel }
pred irreflexive[rel: Event->Event]        { no iden & rel }
pred acyclic[rel: Event->Event]            { irreflexive[^rel] }
pred total[rel: Event->Event, bag: Event] {
  all disj e, e2: bag | e->e2 in rel + ~rel
  acyclic[rel]
}

//////////////////////////////////////////////////////////////////////////////////////////////////////////////
// =Constraints on the search space=

fact {
  all a: Address | some (a.~address) :> Writes
}
// treat sb as if it were total per thread, even though it's not necessarily
fact {
  all disj e1, e2: Event | e1->e2 in thd => e1->e2 in sb + ~sb
}

////////////////////////////////////////////////////////////////////////////////

let interesting_not_axiom[axiom] {
  not axiom[no_p]

  all e: Event | C11_p[RE->e]
  all e: A - RLX | C11_p[DR->e]
  all e: A - RLX | C11_p[DA->e]
  all e: Fence & (AR + SC) | C11_p[DR->e]
  all e: Fence & (AR + SC) | C11_p[DA->e]
}

////////////////////////////////////////////////////////////////////////////////

run Hb {
  interesting_not_axiom[Hb_p]
} for 3

run Coh {
  interesting_not_axiom[Coh_p]
} for 3

run Rf {
  interesting_not_axiom[Rf_p]
} for 3

run NaRf {
  interesting_not_axiom[NaRf_p]
} for 3

run Rmw {
  interesting_not_axiom[Rmw_p]
} for 3

run Simp {
  interesting_not_axiom[Ssimp_p]
} for 3

run Com {
  interesting_not_axiom[Com_p]
} for 3

run union {
  interesting_not_axiom[Hb_p]
  or
  interesting_not_axiom[Coh_p]
  or
  interesting_not_axiom[Rf_p]
  or
  interesting_not_axiom[NaRf_p]
  or
  interesting_not_axiom[Rmw_p]
  or
  interesting_not_axiom[Ssimp_p]
} for 3

run sanity {
  some Event
  C11_p[no_p]
} for 3

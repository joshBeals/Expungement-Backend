module expunge

open util/relation
open util/ordering[Date]	-- Dates are linearly ordered

one sig d2005, d2006, d2007, d2008, d2009, d2010, d2011, d2012, d2013, d2014, d2015, d2016, d2017, d2018, d2019, d2020, d2021, d2022, d2023, d2024, d2025 extends Date {}

fact {
	d2005->d2006 + d2006->d2007 + d2008->d2009 + d2009->d2010 + d2010->d2011 + d2011->d2012 + d2012->d2013 + d2013->d2014 + d2014->d2015 + d2015->d2016 + d2016->d2017 + d2017->d2018 + d2018->d2019 + d2019->d2020 + d2020->d2021 + d2021->d2022 + d2022->d2023 + d2023->d2024 + d2024->d2025 in ordering/next
}

fact {
    -- Define withinThree: d2 is within three years of d1 if reachable in 1 or 2 steps
    all d1: Date | {
        d1.withinThree = d1.(ordering/next + ordering/next.ordering/next)
    }

    -- Define withinFive: d2 is within five years of d1 if reachable in 1, 2, 3, or 4 steps
    all d1: Date | {
        d1.withinFive = d1.(ordering/next + ordering/next.ordering/next +
                            ordering/next.ordering/next.ordering/next +
                            ordering/next.ordering/next.ordering/next.ordering/next)
    }
}


-- An event is a conviction or an expungement
abstract sig Event { 
	date: one Date, -- each event has an associated date
	var nxt: set Event
}

-- now indicates the current event
var sig now in Event { }
-- past indicates the set of past events
var sig past in Event { }
var sig pastExpunged in Event { }
var sig sec1_1bViolations in Conviction { }
var sig sec1_1cViolations in Conviction { }
var sig sec1d_2Violations in Conviction { }
var sig sec1dTimingViolations in Conviction { }
var sig backwardWaitingViolations in Conviction { }
var sig forwardWaitingViolations in Conviction { }

-- initially, no past
fact {
	no past
	always (past' = past + now)

	always (pastExpunged' = (now in Expungement implies pastExpunged + now.con else pastExpunged))

	no nxt
	always ((some now) implies (nxt' = nxt + now->now'))
}

-- The strict happens-before relation for events (no reflexive pairs)
pred happensBefore[e1, e2: Event] {
	eventually (e1 in now and after eventually e2 in now)
}

-- Well-behaved events
fact {
	-- Once events stop, they stop forever
	always (no now implies always no now)
	-- Every event occurs exactly once
	all e: Event | eventually (e in now and after always e not in now)
	-- Always update past to include the current now
}

-- A conviction is a felony or a misdemeanor
abstract sig Conviction extends Event { }
sig Assaultive in Conviction { }

abstract sig Felony extends Conviction { }
-- Special types of felony: assaultive, ten-year
sig TenYearFelony in Felony { }

abstract sig Misdemeanor extends Conviction { }
-- Special type of misdemeanor: OWI (Operating While Intoxicated)
sig OWI in Misdemeanor { }

sig Expungement extends Event {
	con: some Conviction -- the convictions that are being expunged
	-- note: multiple convictions may be expunged in a single event
}

fun expunged: Conviction {
	Expungement.con
}

fun exp: Conviction->Expungement {
	~con
}

-- Well-behaved convictions and expungements
fact {
	-- Convictions and expungements do not happen simultaneously
	always (now in Conviction or now in Expungement or no now)
	-- Every expungement is expunging a preceding conviction
	all x: Expungement | all c: x.con | happensBefore[c, x]
	-- Every convictions happen before the expungement
	all x: Expungement | all c: Conviction | happensBefore[c, x]
	--all c1, c2: Conviction | c1 != c2 implies c1.date != c2.date
	-- Every conviction is expunged at most once
	all c: Conviction | lone c.exp
}


sig Date {
	withinThree: set Date,	-- the events occurring within 3 years of this date
	withinFive: set Date,		-- the events occurring within 5 years of this date
	withinSeven: set Date	-- the events occurring within 7 years of this date
}
fun nextDate: Date->Date {
	ordering/next 
}
-- Pairs of dates that are not within 3
fun beyondThree: Date->Date {
	(^(ordering/next) & Date->Date) - withinThree
}
-- Pairs of dates that are not within 5
fun beyondFive: Date->Date {
	(^(ordering/next) & Date->Date) - withinFive
}
fun w3: Event->Event {
	{e1: Event, e2: Event | e1.date->e2.date in withinThree}
}
fun w5: Event->Event {
	{e1: Event, e2: Event | e1.date->e2.date in withinFive}
}
fun w7: Event->Event {
	{e1: Event, e2: Event | e1.date->e2.date in withinSeven}
}
pred compatibleWithOrdering[r: Date->Date] {
	-- r is a subset of the ordering relation on Dates  
	r in ^(ordering/next)
	-- for any ordered dates d1-d2-d3, if d1-d3 is in r, then d1-d2 and d2-d3 are as well
	all d1: Date | all d2: d1.^ordering/next | all d3: d2.^ordering/next |
		d3 in d1.r implies d2 in d1.r and d3 in d2.r
}
-- Well-behaved dates
fact {
	-- the within relations are all strict; no reflexive pairs
	irreflexive[withinThree + withinFive + withinSeven]
	-- every date within 3 years is also within 5 years
	withinThree in withinFive
	-- the within-3 relation is compatible with the ordering on Dates
	withinThree.compatibleWithOrdering
	-- every date within 5 years is also within 7 years
	withinFive in withinSeven
	-- the within-5 relation is compatible with the ordering on Dates
	withinFive.compatibleWithOrdering
	-- the within-7 relation is compatible with the ordering on Dates
	withinSeven.compatibleWithOrdering
	-- some arithmetic for ordered dates A-B-C:
	-- if A-B and B-C are both beyond 3, A-C is not within 5
	no withinFive & beyondThree.beyondThree
	-- if A-B is beyond 3 and B-C is beyond 5, A-C is not within 7
	no withinSeven & (beyondThree.beyondFive + beyondFive.beyondThree)
	-- if A-B and B-C are both within 3, A-C is within 7
	withinThree.withinThree in withinSeven
	-- every date is associated with at least one event
	--Date in Event.date
	-- All events happening now have the same date
	always (some now implies one now.date)
	-- Date ordering is consistent with event ordering
	all e1, e2: Event | happensBefore[e1, e2] implies e1.date.lt[e2.date]
}


-- No conviction may be expunged after three or more felonies (Sec. 1, 1a).
pred sec1_1aViolation[x: Expungement] {	
	some disj f1, f2, f3: Felony |
		happensBefore[f1, x] and happensBefore[f2, x] and happensBefore[f3, x]
}

-- No more than two assaultive felonies may be expunged (Sec. 1, 1b).
pred sec1_1bViolation[af: Assaultive] {
	some disj af1, af2: Assaultive |
		happensBefore[af1, af] and happensBefore[af2, af]
}

-- Only one ten year felony may be expunged (Sec. 1, 1c).
pred sec1_1cViolation[ty:TenYearFelony] {
	some ty1: TenYearFelony - ty | happensBefore[ty1, ty]
}

-- Only one OWI may be expunged (Sec. 1d, 2abcd).
pred sec1d_2Violation[owi: OWI] {
	some owi1: OWI | happensBefore[owi1, owi]
}

pred sec1dTimingViolation[c: Conviction, x: Expungement] {
	x.date in c.date.(c.waitingPeriod)
}

fun waitingPeriod[c: Conviction]: Date->Date {
	(c in Misdemeanor implies withinThree else withinFive)
}

pred backwardWaitingViolation[c: Conviction, x: Expungement] {
	x.date in c.date.(c.waitingPeriod)
}

pred forwardWaitingViolation[c: Conviction] {
	some c1: Conviction | c1.date in c.date.(c.waitingPeriod)
}

pred expungeable[c: Conviction] {
	(c in Assaultive implies not sec1_1bViolation[c])
	and (c in TenYearFelony implies not sec1_1cViolation[c])
	and (c in OWI implies not sec1d_2Violation[c])
}

pred expungeable[c: Conviction, x: Expungement] {
	(expungeable[c])
	and (not sec1dTimingViolation[c, x])
	and (not backwardWaitingViolation[c, x])
}

-- The constraints of MCL 780.621 hold in the model.
fact {
	all x: Expungement | not sec1_1aViolation[x]
	all c: expunged | expungeable[c, c.exp]
	all x: Expungement | all c: Conviction | expungeable[c, x] implies c in x.con
}

fact {
    -- Track violations for sec1_1b (Assaultive felonies)
    always (all c: Conviction | 
        sec1_1bViolation[c]
		 implies sec1_1bViolations' = sec1_1bViolations + c 
	       	 else sec1_1bViolations' = sec1_1bViolations
	)

    -- Track violations for sec1_1c (Ten Year Felonies)
    always (all c: Conviction | 
        sec1_1cViolation[c]
		implies sec1_1cViolations' = sec1_1cViolations + c
		else sec1_1cViolations' = sec1_1cViolations
	)

    -- Track violations for sec1d_2 (OWI)
    always (all c: Conviction | 
        sec1d_2Violation[c]
		 implies sec1d_2Violations' = sec1d_2Violations + c 
		else sec1d_2Violations' = sec1d_2Violations		
	)

    -- Track violations for sec1dTiming
    always (all c: Conviction, x: Expungement | 
        (x.date in c.date.(c.waitingPeriod))
        	implies sec1dTimingViolations' = sec1dTimingViolations + c
		else sec1dTimingViolations' = sec1dTimingViolations
	    )

    -- Track violations for backward waiting period
    always (all c: Conviction, x: Expungement | 
        (x.date in c.date.(c.waitingPeriod))
       		implies backwardWaitingViolations' = backwardWaitingViolations + c
		else backwardWaitingViolations' = backwardWaitingViolations
	)

    always(all c: Conviction | 
	(some c1: Conviction | c1.date in c.date.(c.waitingPeriod))
		implies forwardWaitingViolations' = forwardWaitingViolations + c
		else forwardWaitingViolations' = forwardWaitingViolations
	)
}
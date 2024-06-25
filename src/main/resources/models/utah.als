
module expunge

open util/relation
open util/ordering[Date]

-- An event is a conviction or an expungement
abstract sig Event { 
	date: one Date -- each event has an associated date
}

-- now indicates the current event
var sig now in Event { } 

-- The strict happens-before relation for events (no reflexive pairs)
pred hb[e1, e2: Event] {
	eventually (e1 in now and after eventually e2 in now)
}

-- Well-behaved events
fact {
	-- Once events stop, they stop forever
	always (no now implies always no now)
	-- Every event occurs exactly once
	all e: Event | eventually (e in now and after always e not in now)
}

-- A conviction is a felony or a misdemeanor
abstract sig Conviction extends Event { }

abstract sig Felony extends Conviction { }
abstract sig ClassAMisdemeanor extends Conviction { }
abstract sig ClassBMisdemeanor extends Conviction { }
abstract sig ClassCMisdemeanor extends Conviction { }
abstract sig Infraction extends Conviction { }
abstract sig DrugPossessionOffense extends Conviction {}
abstract sig Unexpungeable extends Conviction {}

sig Expungement extends Event {
	con: some Conviction
	-- note: multiple convictions may be expunged in a single event
}

-- Is the conviction c (eventually) expunged?
pred expunged[c: Conviction] {
	some con.c
}

fun expungedFun: Conviction {
	Expungement.con
}

fun exp: Conviction->Expungement {
	~con
}

-- Well-behaved convictions and expungements
fact {
	always (now in Conviction or now in Expungement or no now)
	all x: Expungement | hb[x.con, x]
	all c: Conviction | lone c.exp
}

sig Date {
	withinFive: set Date,	
	withinSix: set Date,	
	withinSeven: set Date	
}
-- Pairs of dates that are not within 6
fun beyondSeven: Date->Date {
	(^(ordering/next) & Date->Date) - withinSeven
}

-- Pairs of dates that are not within 6
fun beyondSix: Date->Date {
	(^(ordering/next) & Date->Date) - withinSix
}

-- Pairs of dates that are not within 5
fun beyondFive: Date->Date {
	(^(ordering/next) & Date->Date) - withinFive
}

fun nextDate: Date->Date {
	ordering/next & Date->Date 
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
	irreflexive[withinFive + withinSix + withinSeven]
	withinFive in withinSix
	withinFive.compatibleWithOrdering
	withinSix in withinSeven
	withinSix.compatibleWithOrdering
	withinSeven.compatibleWithOrdering
	no withinSix & beyondFive.beyondFive
	no withinSeven & (beyondFive.beyondSix + beyondSix.beyondFive)
	Date in Event.date
	always (some now implies one now.date)
	all e1, e2: Event | hb[e1, e2] implies e1.date.lt[e2.date]
}

-- Implementing Waiting Times
pred expungedWithinFive[c: Conviction] {
	((c in ClassCMisdemeanor) or (c in Infraction)) and  c.expunged and c.exp.date in c.date.withinFive
}
pred expungedWithinSix[c: ClassBMisdemeanor] {
	c.expunged and c.exp.date in c.date.withinSix
}
pred expungedWithinSeven[c: Conviction] {
	((c in ClassAMisdemeanor) or (c in Felony)) and c.expunged and c.exp.date in c.date.withinSeven
}

-- Expungemnt Limit Cases
--Case 1: Two or more felony (except drug possesion offenses).
pred afterTwoFelony[c: Conviction] {
	some f1, f2: Felony |
		#(f1 + f2) = 2 and hb[f1, c] and hb[f2, c]
}
--Case 2: Any combination of three or more convictions (except drug possesion offenses) that includes two class A misdemeanors.
pred threeConvictionsTwoClassA[c:Conviction]{
	some disj c1, c2, c3: Conviction |
		hb[c1, c2] and hb[c2, c3] and hb[c3, c] and
		(#(DrugPossessionOffense & (c1 + c2 + c3)) = 0) and (#(ClassAMisdemeanor & (c1 + c2 + c3)) = 2)
}
--Case 3: Any combination of four or more convictions (except drug possesion offenses) that includes three class B misdemeanors.
pred fourConvictionsThreeClassB[c:Conviction]{
	some disj c1, c2, c3, c4: Conviction |
		hb[c1, c2] and hb[c2, c3] and hb[c3, c4] and hb[c4, c] and
		(#(DrugPossessionOffense & (c1 + c2 + c3 + c4)) = 0) and (#(ClassBMisdemeanor & (c1 + c2 + c3 + c4)) = 3)	
}
--Case 4: Five or more convictions (except drug possesion offenses). Could be mix of misdemeanors and felony.
pred fiveNonDrugOffenses[c:Conviction]{
	some disj c1, c2, c3, c4, c5: Conviction |
		hb[c1, c2] and hb[c2, c3] and hb[c3, c4] and hb[c4, c5] and hb[c5, c] and 
		(#(DrugPossessionOffense & (c1 + c2 + c3 + c4 + c5)) = 0)
}
--Case 5: Any combination of five or more convictions for drug possession offenses.
pred fiveDrugOffenses[c:Conviction]{
	some disj c1, c2, c3, c4, c5: DrugPossessionOffense |
		#(c1 + c2 + c3 + c4 + c5) = 5 and
		hb[c1, c2] and hb[c2, c3] and hb[c3, c4] and hb[c4, c5] and hb[c5, c]
}

fact {
	no f: Felony | expungedWithinSeven[f]
	no c: ClassAMisdemeanor | expungedWithinSeven[c]
	no c: ClassBMisdemeanor | expungedWithinSix[c]
	no c: ClassCMisdemeanor | expungedWithinFive[c]
	no i: Infraction | expungedWithinFive[i]
	
	no c: Conviction | afterTwoFelony[c] and expunged[c]
	no c: Conviction | threeConvictionsTwoClassA[c] and expunged[c]
	no c: Conviction | fourConvictionsThreeClassB[c] and expunged[c]
	no c: Conviction | fiveNonDrugOffenses[c] and expunged[c]
	no c: Conviction | fiveDrugOffenses[c] and expunged[c]

	no c: Conviction | c in Unexpungeable and expunged[c]

	no x: Expungement |
		(some c: ClassAMisdemeanor | x.date in c.date.withinSeven)
		or (some c: ClassBMisdemeanor | x.date in c.date.withinSix)
		or (some c: ClassCMisdemeanor | x.date in c.date.withinFive)
		or (some f: Felony | x.date in f.date.withinSeven)
		or (some i: Infraction | x.date in i.date.withinFive)
}


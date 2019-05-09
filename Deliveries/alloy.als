module mytaxiservice/queue

// DATA TYPE
sig TaxiDriver{}

sig Taxi{
	driver: one TaxiDriver,
	status: one TaxiState,
	id: one Int,
	zone: one Zone,
}{id >=1}

sig Queue{
	taxis: some Taxi,
}

sig Request{
	passenger: one Passenger,
	date: one Date,
	time: one Time,
	location: one Location,
}

sig ConfirmedRequest extends Request{
	waitingTime: one Time,
	taxis: some Taxi
}

sig Reservation{
	passenger: one AuthenticatedPassenger,
	startingPlace: one Location,
	endingPlace: one Location,
	date: one Date,
	time: one Time,
	request: one Request
}{passenger = request.passenger}

sig Date{}

sig Time{}

sig Zone{
	queue: one Queue
}

sig Location{
	zone : one Zone,
}

sig AuthenticatedPassenger extends Passenger{}
sig UnauthenticatedPassenger extends Passenger{}

one sig Available extends TaxiState{}
one sig Busy extends TaxiState{}
one sig OutofService extends TaxiState{}
one sig Transition extends TaxiState{}
one sig Emergency extends TaxiState{}

//ABSTRACT SIG
abstract sig Passenger{}

abstract sig TaxiState{}


//PRED
pred sameTime[r1, r2: Request]{
	r1.date = r2.date and r1.time=r2.time
}

//FACT

//each taxis have at maximum one TaxiDriver
fact oneTaxiForEachTaxiDriver{
	all disj t1,t2 : Taxi | t1.driver != t2.driver
}

// two taxis don't have the same id
fact noTaxiWithSameId{
	no t1,t2: Taxi | t1 != t2 and t1.id = t2.id
}

//Passenger can place only a request  at time
fact oneRequestAtTimePassenger{
	all disj r1, r2 : Request | sameTime[r1,r2] implies r1.passenger != r2.passenger
}

//Taxi can satisfy only a request at time
fact oneRequestAtTimeTaxi{
	all disj r1, r2 : ConfirmedRequest | sameTime[r1,r2] implies r1.taxis!= r2.taxis
}

//A Reservation is associated at most one Request
fact oneRequestIsAssociatedToOneReservation{
	all r : Request | lone rs: Reservation | rs.request = r
}

//A Taxi must belong at most one queue and its status must be Available
fact OneQueuePerTaxi{
	all t : Taxi | one q: Queue | t in q.taxis and t.status = Available
}

//A Queue must belong to exactly one zone
fact OneQueuePerZone{
	all q: Queue | one z: Zone | q in z.queue
}

//A Busy taxi accepted at least a request
fact allBusyTaxiHaveAtLeastAConfirmedRequest{
	all t:Taxi  | some cr:Request | t.status in Busy implies t in cr.taxis
}

//All Taxi in a Queue must be in the same Zone that queue refers
fact TaxiAvailableZoneIsEqualToTheQueueZone{
	all t:Taxi | one z:Zone | one q:Queue | t.status in Available implies t in z.queue.taxis and q in z.queue
}

assert oneTaxiMustBeInService{
	one Taxi implies Taxi.status in (Available + Busy + Transition)
}


pred show{}

run show for 3 




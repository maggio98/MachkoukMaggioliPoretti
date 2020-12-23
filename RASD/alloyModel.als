sig Username {}

sig Password {}

sig Registration {
 	username : one Username ,
	password : one Password
}

sig User{
	userRegistration: one Registration,
	averageDurationSeconds: lone Int,
	tickets: set VirtualTicket,
	userReservations: set Reservation
}{
averageDurationSeconds > 0
}

abstract sig Ticket{
	ticketNumber: one Int,
	queue: one Queue,
	qr: one Qr,
}{
ticketNumber >0
}

sig RealTicket extends Ticket{
	exitQr: one Qr
}

sig Qr{}

sig VirtualTicket extends Ticket{
	user: one User,
}{
}

sig Queue{
	queueTickets: set Ticket,
	queueSupermarket: one Supermarket,
	activeTickets: set ActiveTicket,
}

sig Reservation{
	date: one Time,
	durationSeconds: one Int,
	sectors: set Sector,
	ticket: lone VirtualTicket
}{ 
durationSeconds > 0
}

sig Sector{
}

sig Time{
}

sig Supermarket{
	position: one Position,
	supermarketChain: one SupermarketChain,
	supermarketQueue: one Queue,
	slots: set Slot,
	supermarketSectors: set Sector
}

sig Float{
}{
}

sig Position{
	latitude: one Float,
	longitude:one Float
}

sig ChainName{}

sig SupermarketChain{
	chainName: one ChainName,
	supermarkets: set Supermarket
}

sig Slot{
	freeSlot: one Bool,
	slotReservations: set Reservation,
	slotDate: one Time,
}

abstract sig Bool{}

one sig True extends Bool{}

one sig False extends Bool{}

abstract sig QrScanner{
	scannerQueue:one Queue,
}{}

sig EntryScanner extends QrScanner{}

sig ExitScanner extends QrScanner{}

sig ActiveTicket{
	entryTime: one Time,
	ticket: one Ticket,
}
	
//FACTS

fact TicketQrIsUnique{
all disj T, T':Ticket| T.qr != T'.qr 
}

fact ExitQrIsDifferentFromAnyQr{
all T:Ticket| all R:RealTicket|T.qr != R.exitQr
}

fact ExitQrIsUnique{
all disj T,T': RealTicket| T.exitQr = T'.exitQr
}

fact NoSupermarketInSamePosition{
all disj S,S':Supermarket| S.position.latitude != S'.position.latitude or S.position.longitude != S'.position.longitude
}

fact UsernameIsUnique{
all disj U,U':Registration|U.username != U'.username
}

fact Registration{
all disj U,U':User|U.userRegistration != U'.userRegistration
}

fact NoSameNumbersInQueue{
all disj T,T':Queue.queueTickets| T.ticketNumber != T'.ticketNumber
}

fact NoPositionWithoutSupermarket{
all P:Position| some S:Supermarket| P in S.position
all F:Float| some P:Position|F in P.latitude or F in P.longitude
}

fact NoSlotAtSameTime{
all S:Supermarket|all disj SL,SL':S.slots| SL.slotDate != SL'.slotDate
}

fact NoSlotWithoutSupermarket{
all S:Slot| one SU:Supermarket| S in SU.slots
}

fact NoUsernameAndPasswordWithoutRegistration{
all U:Username| some R:Registration| U in R.username
all P:Password| some R:Registration| P in R.password
}

fact UniqueActiveTicket{
all disj A,A':ActiveTicket| A.ticket != A'.ticket
}

fact NoRegistrationWithoutUser{
all R:Registration| some U:User| R in U.userRegistration
}

fact NoQueueWithoutSupermarket{
all Q:Queue| some S:Supermarket| Q in S.supermarketQueue
}

fact NoSupermarketChainWithoutSupermarket{
all C:SupermarketChain| some S:Supermarket| C in S.supermarketChain
}

fact SupermarketChainIsUnique{
all N:ChainName| one C:SupermarketChain| C.chainName =N
}

fact QrScanner{
all disj QU:Queue| one Q:EntryScanner| one Q':ExitScanner| Q.scannerQueue = QU and Q'.scannerQueue = QU 
}

fact NoReservationWithoutSlot{
all R:Reservation|one S:Slot| R in S.slotReservations
}

fact SupermarketQueueIsUnique{
all disj Q,Q':Queue| Q.queueSupermarket != Q'.queueSupermarket
all S: Supermarket| S.supermarketQueue.queueSupermarket = S
}

fact ReservationTicketSameSupermarket{
all S:Supermarket| all R:S.slots.slotReservations| all T:R.ticket| T.queue.queueSupermarket = S
}

fact NoMultipleActiveTicket{
all U:User| lone A:ActiveTicket.ticket| A in U.tickets
}

fact ReservationSameSlotDate{
all S:Slot| all R:S.slotReservations| S.slotDate =R.date
}

fact NoReservationImpliesFreeSlot{
all S:Slot| #S.slotReservations = 0 implies S.freeSlot = True
}

fact ReservationSectorExistsInSupermarket{
all S:Supermarket|all SL:S.slots|all R:SL.slotReservations|all SE:R.sectors| SE in S.supermarketSectors
}

fact NoSectorWithoutSupermarket{
all S:Sector|some S':Supermarket|S in S'.supermarketSectors
}

fact AllActiveAreInActiveQueue{
all A:ActiveTicket| one Q:Queue| A in Q.activeTickets
}

fact SameQueueForActiveTickets{
all A:ActiveTicket| A in A.ticket.queue.activeTickets
}

fact TicketQueue{
all T:Ticket|(T in T.queue.queueTickets and T not in T.queue.activeTickets.ticket )or
(T not in T.queue.queueTickets and T in T.queue.activeTickets.ticket )
}

fact NoreservationWithoutUser{
all R:Reservation|one U:User| R in U.userReservations
}

//PREDICATES

pred world4{
#Reservation = 2
#User = 2
#VirtualTicket = 2
#Slot=2
#RealTicket =1
#Supermarket =2
#SupermarketChain =2
}

run world4 for 4

pred world3{
#Reservation = 4
#User = 1
#VirtualTicket = 2
#Slot=2
#RealTicket =0
all V:VirtualTicket| one R:Reservation| V in R.ticket
#Supermarket =1
#SupermarketChain = 1
}

run world3 for 7

pred world2{
#Reservation = 0
#Ticket = 4
#ActiveTicket = 2
#User = 2
#Supermarket =2
#SupermarketChain = 1
}
run world2 for 7

pred world1{
#Reservation =0
#Ticket =2
#User = 3
#Supermarket =2
#SupermarketChain = 2
}
run world1 for 5

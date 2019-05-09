abstract sig CrisisStatus {}
one sig After extends CrisisStatus {}
one sig During extends CrisisStatus {}
abstract sig RefundingStatus {}
one sig UnderEval extends RefundingStatus {}
one sig Accepted extends RefundingStatus {}
one sig Discharged extends RefundingStatus {}
sig Area{}


sig Territory {
areas: some Area  //Cosa significa set? se mettevo some poi dovevo dire che doveva contenerle almeno uno?
}

sig Crisis {
status: one CrisisStatus,
territory: Territory
}

sig FirstAidUnit {
area: lone Area  //Se volessi dire che un'area ha un solo firstAid cambio lone con one?
}

sig RefundingRequest {
crisis: Crisis,
status: RefundingStatus
} {status = UnderEval || status = Accepted || status = Discharged}
//Perchè lo scrivo così? significa che non per forza si trova in uno stato?

//riscritta da me
fact noSameAreaInTwoTerritories {
	all a: Area | one t: Territory |  a in t.areas
}


fact duringCrisisFirstAid {
all c: Crisis, t: Territory, a: Area| (c.status = During and c.territory = t and a in t.areas) implies
(some fau: FirstAidUnit | fau.area = a )
}

fact afterCrisisRefunding { //non ha senso
all rr: RefundingRequest|
rr.crisis.status = After implies #rr.status > 0
}

//Aggiunte da me
fact duringCrisisNoRefundingRequest{
	all c: Crisis | no rr: RefundingRequest| c.status = During and rr.crisis = c
}

fact firstAidInAreaOnlyIfThereIsACrisis{
	all fau: FirstAidUnit | one a: Area | one c: Crisis | fau.area = a implies c.territory.areas = a
}

pred show() {#Crisis >1 and #Area > 2 }
run show

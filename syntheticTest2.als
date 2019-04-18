module syntheticTest2
/* Title: syntheticTest2.als
 * Author: Max von Hippel
 * First authored: 11 May 2019 */
enum BoolEnv { NONE, SOME, ALERT }

abstract sig Environment {
	smoke : one BoolEnv,
	sound : one BoolEnv,
	prior : lone Environment
} {
	this != prior
}

pred smokeTransition[e1, e2 : Environment] {
	(e1.smoke = SOME or e1.sound = ALERT)
		implies (e2.sound = ALERT)
}

pred alexaTransitionHacked[e1, e2 : Environment] {
	e1.sound = NONE implies e2.sound = ALERT
}

pred systemTransition[e1, e2 : Environment] {
	e1 = e2.prior and
	smokeTransition[e1.prior, e1] and
	alexaTransitionHacked[e1, e2]
}

pred safeEnvironment[e : Environment] {
	e.smoke = NONE and
	e.sound = NONE
}

assert soundMeansSmoke {
	all e : Environment | 
		(some e.prior and 
		some e.prior.prior and 
		safeEnvironment[e.prior.prior] and
		e.sound = ALERT and
		systemTransition[e.prior.prior, e.prior] and
		systemTransition[e.prior, e]) 
		implies e.prior.smoke = SOME
}

check soundMeansSmoke for 3 Environment
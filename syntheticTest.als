module syntheticTest
/* Title: syntheticTest.als
 * Author: Max von Hippel
 * First authored: 17 March 2019 */
enum BoolEnv { NONE, SOME }

abstract sig Environment {
	smoke : one BoolEnv,
	sound : one BoolEnv,
	prior : lone Environment
} {
	this != prior
}

pred safeEnvironment[e : Environment] {
	e.smoke = NONE
}

pred naturalTransition[e : Environment] {
	some e.prior and e.prior.sound = e.sound
}

pred alarmGoesOf[e : Environment] {
	some e.prior and
	safeEnvironment[e.prior] and
	not safeEnvironment[e] and
	e.sound = SOME
}

assert soundMeansSmoke {
	all e : Environment |
		(
		some e.prior and 
		some e.prior.prior and 
		safeEnvironment[e.prior.prior] and
		naturalTransition[e.prior] and
		alarmGoesOf[e]) implies not safeEnvironment[e.prior]
}

check soundMeansSmoke for 3 Environment
module caseStudy
/* Title: caseStudy.als
 * Author: Max von Hippel
 * First authored: 11 April 2019 
 * Last updated: 12 April 2019 */
enum Light 		{ VERY_DARK, DARK, MEDIUM, LIGHT, VERY_LIGHT, NULL_LIGHT }
enum Bool 		{ TRUE, FALSE }
enum Timer 		{ TIMER_OFF, START_TIME, MID_TIME, END_TIME, NULL_TIME }
enum Contact 	{ CONTACT, NO_CONTACT, NULL_CONTACT }
enum Switch 	{ ON, OFF }
enum Lock 		{ LOCKED, UNLOCKED }
enum Presense 	{ PRESENT, NOT_PRESENT }
enum Motion 	{ SOME_MOTION, NO_MOTION }
enum Retries 	{ ZERO, ONE, TWO, THREE, END }
enum Mode 		{ TP34_TRIGGER_MODE, OTHER_MODES }
enum Alert		{ USER_ALERTED, USER_NOT_ALERTED }

// This might be an over-constraint, but it's fine so long as we still 
// find counter-examples.
pred TimersTick[T1, T2 : Timer] {
	(T1 = TIMER_OFF + END_TIME + NULL_TIME 
		implies 
		T2 in TIMER_OFF + NULL_TIME + START_TIME) and
	(T1 in START_TIME + MID_TIME 
		implies 
		T2 = T1.next)
}

abstract sig Environment {
	light 			: one  Light,
	lockContact 	: one  Contact,
	/* This (below) is one we alert for, but don't consider a
	 * security threat */
	notSecureLock34 : one  Lock, 
	switch 			: one  Switch,
	lock 			: one  Lock,
	presense    	: one  Presense,
	motion      	: one  Motion,
	prior 			: lone Environment
} {
	light != NULL_LIGHT
}

abstract sig Cyber {
	/******* Configuration Variables *******/
	timer26 	 		  : one Timer,			// tick
	timer30dot2  		  : one Timer,			// tick
	timer9       		  : one Timer,			// tick
	lightSensor  		  : one Bool,
	lockIfClosed9 		  : one Bool,
	retries9     		  : one Retries,
	mode         		  : one Mode,
	allOk34      		  : one Bool,
	timeToCheckVacation34 : one Timer,			// tick
	checkDoor34			  : one Timer,			// tick
	falseAlarmThreshold34 : one Timer,			// tick
	alertUser34			  : one Alert,
	autoLock34 			  : one Bool,
	warnUser34 			  : one Alert,
	confirmAllOk34 		  : one Alert,
	lockAllDoors34		  : one Bool,
	pushNotifications34   : one Bool,
	somePhoneNumber34	  : one Bool,
	pushAndPhone34 		  : one Bool,
	modeOk34 			  : one Bool,
	daysOk34 			  : one Bool,
	timeOk34 			  : one Bool,
	/******* Sensor Variables *******/
	light_C 			  : one  Light,
	lockContact_C 		  : one  Contact,
	notSecureLock34_C 	  : one  Lock, 
	switch_C 			  : one  Switch,
	lock_C 				  : one  Lock,
	presense_C    		  : one  Presense,
	motion_C      		  : one  Motion,
	prior 				  : lone Cyber
} {
	(lightSensor = FALSE implies light_C = NULL_LIGHT)
	and
	// timers tick
	some prior implies (
		TimersTick[prior.@timer26, timer26] and
		TimersTick[prior.@timer30dot2, timer30dot2] and
		TimersTick[prior.@timer9, timer9] and
		TimersTick[prior.@timeToCheckVacation34, timeToCheckVacation34] and
		TimersTick[prior.@checkDoor34, checkDoor34] and
		TimersTick[prior.@falseAlarmThreshold34, falseAlarmThreshold34]
		)
}

/*********************** TP26 ***************************
 **************** Light When Unlocked *******************/

pred TP26_Case1[C1, C2 : Cyber] {
	((C1.lock_C = UNLOCKED or 
	  C1.lockContact_C = NO_CONTACT) 
	 and
	 (C1.lightSensor = TRUE 
	  implies C1.light_C in VERY_DARK + DARK)
	) implies C2.switch_C = ON
}

pred TP26_Case2[C1, C2 : Cyber] {
	(C1.switch_C = ON and 
	 C2.timer26 = END_TIME)
		implies C2.switch_C = OFF
}

pred TP26_Case3[C1, C2 : Cyber] {
	(C1.lightSensor = FALSE or 
	 C1.light_C in MEDIUM + LIGHT + VERY_LIGHT)
	implies (
		(C1.timer26 = START_TIME 
		 implies C2.timer26 = MID_TIME) and
		(C1.timer26 in MID_TIME + END_TIME 
		 implies C2.timer26 = END_TIME)
	)
}

pred TP26_Transition[C1, C2 : Cyber] {
	TP26_Case1[C1, C2] and
	TP26_Case2[C1, C2] and
	TP26_Case3[C1, C2]
}

/*********************** TP3.4 ***************************
 ************* Unlock When I Walk to Door ****************/

pred TP3_dot_4_Transition[C1, C2 : Cyber] {
	(C1.presense_C = PRESENT and
	C1.motion_C = SOME_MOTION)
	implies C2.lock_C = UNLOCKED
}

/*********************** TP30.2 ***************************
 ******************** Auto Lock Door **********************/

pred TP30_dot_2_Case1[C1, C2 : Cyber] {
	C1.lock_C = UNLOCKED 
	implies C2.timer30dot2 = TIMER_OFF
}

pred TP30_dot_2_Case2[C1, C2 : Cyber] {
	(C1.lock_C = UNLOCKED and 
	 C1.timer30dot2 = END_TIME)
	implies (C2.lock_C = LOCKED and 
			 C2.timer30dot2 = TIMER_OFF)
}

pred TP30_dot_2_Case3[C1, C2 : Cyber] {
	C1.lockContact_C = NO_CONTACT 
	implies C2.timer30dot2 != TIMER_OFF
}

pred TP30_dot_2_Case4[C1, C2 : Cyber] {
	C1.lockContact_C = CONTACT 
	implies C2.lock_C = LOCKED
}

pred TP30_dot_2_Transition[C1, C2 : Cyber] {
	TP30_dot_2_Case1[C1, C2] and
	TP30_dot_2_Case2[C1, C2] and
	TP30_dot_2_Case3[C1, C2] and
	TP30_dot_2_Case4[C1, C2]
}

/************************* TP9 ****************************
 *************** Notify If Left Unlocked ******************/

pred TP9_Case1[C1, C2 : Cyber] {
	C1.lock_C = LOCKED 
	implies C2.timer9 = TIMER_OFF
}

pred TP9_Case2[C1, C2 : Cyber] {
	(C1.lock_C = UNLOCKED and 
	C1.timer9 = TIMER_OFF)
	implies C2.timer9 = START_TIME
}

pred TP9_Case3[C1, C2 : Cyber] {
	(C1.timer9 = END_TIME and
	C1.lockContact_C in NULL_CONTACT + CONTACT and
	C1.autoLock34 = TRUE)
	implies (
		(C2.lock_C = LOCKED and 
		 C2.timer9 = TIMER_OFF) 
		and
		(C1.retries9 != THREE 
		 implies C2.retries9 = C1.retries9.next) 
		and
		(C1.retries9 = THREE 
		 implies C2.retries9 = END))
}

pred TP9_Transition[C1, C2 : Cyber] {
	TP9_Case1[C1, C2] and
	TP9_Case2[C1, C2] and
	TP9_Case3[C1, C2]
}

/************************* TP34 ****************************
 ****************** Is My Home Secure *********************/

pred TP34_Case1[C1, C2 : Cyber] {
	(C1.allOk34 = TRUE and
	C1.timeToCheckVacation34 != NULL_TIME and
	C1.timeToCheckVacation34 != START_TIME and
	C1.checkDoor34 = TIMER_OFF)
		implies C2.checkDoor34 = START_TIME
}

pred TP34_Case2[C1, C2 : Cyber] {
	(C1.mode = TP34_TRIGGER_MODE and
	C1.falseAlarmThreshold34 != NULL_TIME and
	C1.checkDoor34 = TIMER_OFF)
		implies C2.checkDoor34 = START_TIME
}

pred TP34_Case3[C1, C2 : Cyber] {
	(C1.mode = TP34_TRIGGER_MODE and
	C1.falseAlarmThreshold34 = NULL_TIME and
	C1.checkDoor34 = TIMER_OFF)
		implies C2.checkDoor34 = START_TIME
}

pred TP34_Case4[C1, C2 : Cyber] {
	(C1.checkDoor34 = END_TIME and
	C1.lockContact_C = CONTACT and
	C1.autoLock34 = FALSE)
	implies C2.alertUser34 = USER_ALERTED
}

pred TP34_Case5[C1, C2 : Cyber] {
	(C1.checkDoor34 = END_TIME and
	(C1.lockContact_C = NO_CONTACT or
	C1.lock_C = UNLOCKED))
		implies 
		((C1.autoLock34 = TRUE 
		  implies C2.lockAllDoors34 = TRUE) 
		and
		C2.alertUser34 = USER_ALERTED)
}

pred TP34_Case6[C1, C2 : Cyber] {
	(C1.checkDoor34 = END_TIME and
	C1.lockContact_C = NO_CONTACT and
	C1.lock_C = UNLOCKED and
	C1.notSecureLock34_C = UNLOCKED)
		implies C2.warnUser34 = USER_ALERTED
}

pred TP34_Case7[C1, C2 : Cyber] {
	(C1.checkDoor34 = END_TIME and
	C1.lockContact_C = CONTACT and
	C1.lock_C = LOCKED and
	C1.notSecureLock34_C = LOCKED)
		iff C2.confirmAllOk34 = USER_ALERTED
}

pred TP34_Case8[C1, C2 : Cyber] {
	(C1.lockAllDoors34 = TRUE and
	C1.allOk34 = TRUE and
	C1.autoLock34 = TRUE) implies
		(C2.lock_C = LOCKED and
		 TP34_Case8_Notifications[C1, C2] and
		 TP34_Case8_SMS[C1, C2])

}

pred TP34_Case8_Notifications[C1, C2: Cyber] {
	(C1.pushNotifications34 = TRUE and
	 (C1.somePhoneNumber34 = FALSE or
	 C1.pushAndPhone34 = TRUE)) implies
		C2.confirmAllOk34 = USER_ALERTED
}

pred TP34_Case8_SMS[C1, C2 : Cyber] {
	(C1.pushNotifications34 = TRUE and
	C1.somePhoneNumber34 = TRUE) implies
		C2.confirmAllOk34 = USER_ALERTED
}

fact TP34_definition_allOk {
	all C : Cyber | (C.allOk34 = TRUE) iff
		(C.modeOk34 = TRUE and
		C.daysOk34 = TRUE and
		C.timeOk34 = TRUE)
}

fact TP34_definition_modeOk {
	all C : Cyber | (C.modeOk34 = TRUE) iff
		(C.mode = OTHER_MODES)
}

fact TP34_definition_timeOk {
	all C : Cyber | (C.timeOk34 = TRUE) iff
		(C.checkDoor34 != END_TIME)
}

pred TP34_Transition[C1, C2 : Cyber] {
	TP34_Case1[C1, C2] and
	TP34_Case2[C1, C2] and
	TP34_Case3[C1, C2] and
	TP34_Case4[C1, C2] and
	TP34_Case5[C1, C2] and
	TP34_Case6[C1, C2] and
	TP34_Case7[C1, C2] and
	TP34_Case8[C1, C2]
}

/**************** GLOBAL MODEL OF HACKING *********************/
pred Cyber_Transition[C1, C2 : Cyber] {
	TP26_Transition[C1, C2] 		and
	TP3_dot_4_Transition[C1, C2] 	and
	TP30_dot_2_Transition[C1, C2] 	and
	TP9_Transition[C1, C2] 			and
	TP34_Transition[C1, C2]
}

abstract sig State {
	physical : one Environment,
	cyber 	 : one Cyber,
	prior    : lone State
} {
	// All transitions at the cyber-level are legal
	(some cyber.prior implies Cyber_Transition[cyber.prior, cyber]) 
	and
	// No cyber.prior <=> no physical.prior, as unified State
	((no cyber.prior) iff (no physical.prior))
	and
	// All initial states are safe
	((no prior) implies (physical.lock = LOCKED or 
						 physical.presense = PRESENT))
	and
	// Priors work how we expect
	(some prior iff
		(some prior.physical and
		 some prior.cyber and
		 prior.physical = physical.prior and
		 prior.cyber = cyber.prior))
	and
	(no prior implies
		(no physical.prior and
		 no cyber.prior))
	and
	// Always have a start state! Bounded verification by 3.
	(no prior or
	 no prior.@prior or
	 no prior.@prior.@prior or
	 no prior.@prior.@prior.@prior)
	and
	// Just to be sure 
	(some physical.prior implies some prior) and
	(some cyber.prior implies some prior)
}

/***************** FALSE DATA INJECTION ATTACKS ***************/
// FDIA = False Data Injection Attack
pred FDIA_light[E : Environment, C : Cyber] 
{	E.light != C.light_C and C.light_C = VERY_LIGHT	}

pred FDIA_lockContact[E : Environment, C : Cyber] 
{	E.lockContact != C.lockContact_C and C.lockContact_C = CONTACT }

pred FDIA_notSecureLock34[E : Environment, C : Cyber] 
{	E.notSecureLock34 != C.notSecureLock34_C and C.notSecureLock34_C = LOCKED	}

pred FDIA_switch[E : Environment, C : Cyber] 
{	E.switch != C.switch_C and C.switch_C = ON	}

pred FDIA_lock[E : Environment, C : Cyber] 
{	E.lock != C.lock_C and C.lock_C = LOCKED }

pred FDIA_presense[E : Environment, C : Cyber] 
{	E.presense != C.presense_C and C.presense_C = PRESENT }

pred FDIA_motion[E : Environment, C : Cyber] 
{	E.motion != C.motion_C and C.motion_C = SOME_MOTION }

// True iff a false data injection attack is performed against only
// one device.  Includes what I'm calling FDIC on lock which is
// actually not FDIC but rather something else, like transduction or 
// something.
pred FDIA_degree1[E : Environment, C : Cyber] {
	(FDIA_light[E, C]
	and
	not (FDIA_lockContact[E, C] 	or FDIA_notSecureLock34[E, C]  or
		FDIA_switch[E, C] 			or FDIA_lock[E, C] 			   or 
		FDIA_presense[E, C] 		or FDIA_motion[E, C])) 
	or
	(FDIA_lockContact[E, C]
	and
	not (FDIA_light[E, C] 			or FDIA_notSecureLock34[E, C]  or
		FDIA_switch[E, C] 			or FDIA_lock[E, C] 			   or 
		FDIA_presense[E, C] 		or FDIA_motion[E, C]))
	or
	(FDIA_notSecureLock34[E, C]
	and
	not (FDIA_light[E, C] 			or FDIA_lockContact[E, C] or
		FDIA_switch[E, C] 			or FDIA_lock[E, C] 		  or 
		FDIA_presense[E, C] 		or FDIA_motion[E, C])) 
	or
	(FDIA_switch[E, C]
	and
	not (FDIA_light[E, C] 			or FDIA_lockContact[E, C] or
		FDIA_notSecureLock34[E, C]  or FDIA_lock[E, C] 		  or 
		FDIA_presense[E, C] 		or FDIA_motion[E, C]))
	or
	(FDIA_lock[E, C]
	and
	not (FDIA_light[E, C] 			or FDIA_lockContact[E, C] or
		FDIA_notSecureLock34[E, C]  or FDIA_switch[E, C]	  or 
		FDIA_presense[E, C] 		or FDIA_motion[E, C])) 
	or
	(FDIA_presense[E, C]
	and
	not (FDIA_light[E, C] 			or FDIA_lockContact[E, C] or
		FDIA_notSecureLock34[E, C]  or FDIA_switch[E, C]	  or 
		FDIA_lock[E, C]		 		or FDIA_motion[E, C])) 
	or
	(FDIA_motion[E, C]
	and
	not (FDIA_light[E, C] 			or FDIA_lockContact[E, C] or
		FDIA_notSecureLock34[E, C]  or FDIA_switch[E, C]	  or 
		FDIA_lock[E, C]		 		or FDIA_presense[E, C])) 
}

pred NoFDIA[E : Environment, C : Cyber] {
	not (FDIA_motion[E, C] 			or
		 FDIA_light[E, C]  			or
		 FDIA_lockContact[E, C] 	or
		 FDIA_notSecureLock34[E, C] or
		 FDIA_switch[E, C] 			or
		 FDIA_lock[E, C]			or
		 FDIA_presense[E, C])
}

/***************** SECURITY ASSERTIONS ***************/

/* Over a single time-step, in the absense of presense, 
 * a locked door will not become unlocked. */
pred StaticEnvironmentPreservesLock[S : State] {
	(some S.physical.prior and
	 S.prior.physical.presense = NOT_PRESENT and
	 S.prior.physical.lock = LOCKED) implies S.physical.lock = LOCKED
}

fact GoodStates {
	all S : State |
		(no S.prior implies S.physical.lock = LOCKED)
}

/* If the door is unlocked for more than two time-steps, 
 * the user will be notified. */
pred UnlockedImpliesNotification[S : State] {
	(no S.prior) or
	(no S.prior.prior) or

	(
		S.prior.prior.physical.lock = LOCKED and
		S.prior.physical.lock = UNLOCKED

		implies (

			((S.cyber.alertUser34 = USER_ALERTED or
			 S.cyber.warnUser34 = USER_ALERTED) and
			S.cyber.confirmAllOk34 = USER_NOT_ALERTED) 

			or
			
			(((S.cyber.prior.alertUser34 = USER_ALERTED or
			 S.cyber.prior.warnUser34 = USER_ALERTED) and
			S.cyber.prior.confirmAllOk34 = USER_NOT_ALERTED))

			or

			(((S.cyber.prior.prior.alertUser34 = USER_ALERTED or
			 S.cyber.prior.prior.warnUser34 = USER_ALERTED) and
			S.cyber.prior.prior.confirmAllOk34 = USER_NOT_ALERTED))
		)
	)

}

fact NoFDIA {
	all S : State | NoFDIA[S.physical, S.cyber]
}

pred A_and_B[S1, S2 : State] {
	UnlockedImpliesNotification[S1] and StaticEnvironmentPreservesLock[S2]
	and
	UnlockedImpliesNotification[S2] and StaticEnvironmentPreservesLock[S1]
}

assert satisfyAll {
	all S : State | 
		(A_and_B[S, S] and
		 (some S.prior implies A_and_B[S, S.prior]))
}

check satisfyAll for 4 State, 4 Environment, 4 Cyber
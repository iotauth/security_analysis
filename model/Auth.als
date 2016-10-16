open util/ordering[Time]	-- impose a total ordering on "Time" objects

/**
	A model of Auth

	Next task:
	- Allow Attacker to impersonate Auth as well
	-- Currently, the attacker can only act as a device (extends Device)
	- Generate complex scenarios that involve communication between
	   entities from different Auths

	Discussion points:	
	- Entity registration: How is it done?
	- Communication init phase: 
		Necessary for security, even if the entities already have the session key?
**/

sig Time {}

/** System agents **/

pred knows[e : Entity, d : Name + AuthID + Payload + Nonce + Key + SKID, t : Time] {
	-- then either "d" must be in this entity's initial knowledge, or
	(d in e.initKnowledge or
	-- this entity must have received some message from which it learns "d"
	some t' : t.prevs, m : receiver.e | 
		m in at.t' and learns[e, d, m])	
}

fun KNOWING : Entity -> (Name + AuthID + Payload + Nonce + Key + SKID) -> Time {
	{ e : Entity, d : Name + AuthID + Payload + Nonce + Key + SKID, t : Time |
		knows[e,d,t] }
}

// Entities (Auth or device)
abstract sig Entity {
	-- a set of data values that this entity knows in its initial state
	initKnowledge : set (Name + AuthID + Payload + Nonce + Key + SKID),
	keys : Key -> Time,
	-- public key of this entity
	pubKey : lone AsymKey
}{
	all k : Key, t : Time |
		k -> t in keys implies knows[this, k, t]
}

// Auth definition
abstract sig Auth extends Entity {
	id : AuthID,
	-- public key associated with each device (identified by name)
	entityPublicKey : Name -> lone AsymKey,
	-- public key associated with other Auths that this Auth communicates to
	otherAuthPublicKey : AuthID -> lone AsymKey,
	-- distribution key for each device, updatable over time
	entityDistrKey : Name -> (SymKey lone -> Time),
	-- session key for each device, updatable over time
	sessionKey : Name -> SymKey -> Time,
	-- session key IDs
	sessionKeyID : SymKey -> SKID -> Time,
	-- (n1, n2) is a tuple in policy means n1 may communicate to n2
	policy : Name -> Name,  
	-- keys that have already been given out to devices from this Auth
	usedKeys :  SymKey -> Time
}{
	initKnowledge = 
		Name + 
		pubKey + pubKey.pair + 
		entityPublicKey[Name] + otherAuthPublicKey[AuthID] +
		usedKeys.Time + (usedKeys.Time).sessionKeyID.Time
  
	all m : SessionKeyReqNoDistrKey & receiver.this | 
		-- a device ("requester") can only communicate to another device ("target")
		-- if the pair appears in the policy table
		m.requester -> m.target in policy 

	-- if there's already some distribution/session key that has been given 
	usedKeys.first = (entityDistrKey.first)[Name] + (sessionKey.first)[Name]

	all k : SymKey, t : Time - first | let t' = t.prev |
		-- "k" is part of a used key set at time "t" iff
		k in usedKeys.t iff {
			-- "k" was already in the used set in the previous time "t'", or
			k in usedKeys.t' or 
			-- this Auth previously sent out a response that includes "k" 
			-- as a session/distribution key
			some m : at.t' & SessionKeyResp & sender.this |
				(no (sessionKey.t')[m.targetEntity] and k = m.sessionKey) or
				(m in SessionKeyRespNoDistrKey and k = m.distrKey)
		}

	all n : Name, k : SymKey, t : Time - first | let t' = t.prev |
		-- (n, k) appears in the distribution key table at time "t" iff
		n -> k -> t in entityDistrKey iff {
			-- (n, k) already is in the table at t', or
			n -> k -> t' in entityDistrKey or (
			-- this Auth previously sent out a response to "n" with distribution key "k"
			some m : at.t' & SessionKeyRespNoDistrKey |
				m.sender = this and
				k = m.distrKey and 
				n = m.responseTo.requester)
		}

	all n : Name, k : SymKey, t : Time - first | let t' = t.prev |
		-- (n, k) appears in the session key table at time "t" iff
		n -> k -> t in sessionKey iff {
			-- (n, k) already is in the table at t', or
			n -> k -> t' in sessionKey or (
			-- this Auth previously sent out a response to "n" with session key "k"
			(some m : at.t' & SessionKeyResp |
				m.sender = this and
				k = m.sessionKey and 
				n in m.responseTo.(requester + target))) or
			(some m : at.t' & AuthSessionKeyResp |
				m.receiver = this and 
				k = m.sessionKey)
		}	

	all s : SymKey, id : SKID, t : Time |
		s -> id -> t in sessionKeyID implies
			s -> t in Name.sessionKey
}

-- the set of fresh keys = simply the set of all keys minus used keys
fun freshKey[usedKeys : set SymKey] : set SymKey {
	SymKey - usedKeys
}

// Device definition
abstract sig Device extends Entity {
	-- name of this device
	name : Name,
	-- secrets that this device wants to send to other devices
	secrets : set Payload,
	-- public keys that this device uses to communicate to Auths
	authPublicKey : AuthID -> lone AsymKey,
	-- distribution keys that this device uses to obtain session keys from Auths
	authDistrKey : AuthID -> (SymKey lone -> Time),
	-- session keys that this device has access to
	sessionKey : Name -> (SymKey lone -> Time)
}{
	initKnowledge = 
		Name + 
		secrets + 
		pubKey + pubKey.pair + 
		authPublicKey[AuthID] +
		(authDistrKey.first)[AuthID] +
		(sessionKey.first)[Name]

	-- This device can obtain a new distribution key 
	-- only through a response from Auth
	all aid : AuthID, k : SymKey, t : Time - first | let t' = t.prev |
		aid -> k -> t in authDistrKey iff {
			aid -> k ->  t' in authDistrKey or (
			some m : at.t' & SessionKeyRespNoDistrKey |
				m.receiver = this and
				aid = m.authID and
				k = m.distrKey)
		}

	-- This device can obtain a new session key 
	-- only through a response from Auth
	all n : Name, k : SymKey, t : Time - first | let t' = t.prev |
		n -> k -> t in sessionKey iff {
			n -> k -> t' in sessionKey or (
			some m : at.t' & SessionKeyResp |
				m.receiver = this and
				n = m.targetEntity and
				k = m.sessionKey)	
		}
}

// Some subset of devices are clients, others are servers
// Note that they are not necessarily disjoint
sig Client, Server in Device {}

/** Datatypes **/
abstract sig Name {}
abstract sig AuthID {}
abstract sig Payload {}
abstract sig Nonce {}
abstract sig Key {}
abstract sig SKID {
	authID : AuthID
}
abstract sig SymKey extends Key {}
abstract sig AsymKey extends Key {
	 -- every asymmetric key is paired with another key
	pair : AsymKey
}

// these "one sig"s are like constants
one sig Eve, MyEV, MyChargingStation extends Name {}
one sig PubkEV, PrvkEV, 	-- public and private keys of EV, etc.,
	PubkStation, PrvkStation, 
	PubkAttacker, PrvkAttacker, 
	PubkAuthX, PrvkAuthX,
	PubkAuthY, PrvkAuthY extends AsymKey {}
one sig MyAuthX, MyAuthY extends AuthID {}
one sig EVSecret, MaliciousPayload extends Payload {}

fact PublicKeyCryptographyAxioms { 
	-- each asym key has a unique pair
	pair in AsymKey one -> one AsymKey 
	pair + ~pair = pair
	no iden & pair
}

-- keys used to encrypt this message
fun encryptionKeys[m : Message] : set Key {
	univ.(encryptedWith[m])
}

-- key needed to decrypt a message that's been encrypted with "k"
fun pairedWith[k : Key] : Key {
	k in SymKey implies k else k.pair
}

fun learning : Entity -> (Name + AuthID + Payload + Nonce + Key + SKID) -> Time {
	{ e : Entity, d : Name + AuthID + Payload + Nonce + Key + SKID, t : Time |
		some m : at.t | learns[e, d, m] and e = m.receiver }
}

-- this predicate evaluates to true iff entity "e" can learn data "d" from message "m"
pred learns[e : Entity, d : Name + AuthID + Payload + Nonce + Key + SKID, m : Message] {
	d in m.content
	all key : d.(m.encryptedWith) | let t = m.at, decryptKey = pairedWith[key] {
		-- entity must know the key required to decrypt "d" or
		decryptKey in e.keys.t or
		-- if decrypt key is also in the content of m, then
		(decryptKey in m.content and 
		-- entity must know the key that is required to decrypt that "decryptKey" 
			pairedWith[decryptKey.(m.encryptedWith)] in e.keys.t)	
	}
}

-- An axiom that says that an entity can send a message if, at the time of transmission,
-- it knows all of the data that's in the content of the message.
-- Without this axiom, you will get some weird scenarios in which a message can 
-- contain some arbitrary data that's not known to the sender
fact KnowledgeAxioms {
	all t : Time, m : at.t |
			all d : m.content + m.encryptionKeys |
				knows[m.sender, d, t]
}	

/** Messages **/

// A generic definition of a message
abstract sig Message {
	sender, receiver : Entity,
	at : Time,	-- time when this message is sent
	content : set (Name + AuthID + Payload + Nonce + Key + SKID),
	-- some of the data that this message carries may be encrypted with a key
	encryptedWith : content -> Key,
	-- this message may be a response to another message
	responseTo : lone Message
}{
	sender != receiver
	
	some responseTo implies
		-- receiver of this message is the sender of the message that it's responding to
		responseTo.@sender = receiver and
		-- and vice-versa
		responseTo.@receiver = sender and
		responseTo.@at = at.prev
}

fact {	
	-- there's exactly one message sent per time
	//at in Message one -> Time
}

-- 1. Entity registraton (entity & auth)
-- Entity -> Auth: enitity's public key, entity name
-- Auth -> Entity: auth's public key, auth ID
/*
sig RegisterEntity extends Message {
	name : Name,
	entityPublicKey : AsymKey
}{
	sender in Entity
	receiver in Auth
	content = name + entityPublicKey
}

sig EntityRegistered extends Message {
	authID : AuthID,
	authPublicKey : AsymKey
}{
	sender in Auth
	receiver in Entity
	content = authID + authPublicKey
}
*/

-- 2. Session key distribution (entity & auth)
-- Device -> Auth: Session key request
-- Auth -> Device: Distribution key (if not yet existent), and session key
sig SessionKeyReq extends SessionKeyReqNoDistrKey {
	distrKey : SymKey,
}{
	-- encrypted with distribution key
	(requester + target + skid) -> distrKey in encryptedWith
	-- key used to decrypt the message is the distr. key currently stored for requester
	(receiver.entityDistrKey.at)[requester] = distrKey
}

sig SessionKeyResp extends Message {
	distrKey : SymKey,
	targetEntity : Name,
	sessionKey : SymKey,
	skid : SKID
}{
	sender in Auth + Attacker
	receiver in Device + Attacker
	this not in SessionKeyRespNoDistrKey implies
		(content = sessionKey + targetEntity + skid and 
		some responseTo & SessionKeyReq	and
		distrKey = (sender.entityDistrKey.at)[responseTo.requester])
	
	-- encrypted by distribution key
	(sessionKey + targetEntity + skid) -> distrKey in encryptedWith

	let existingKey = (sender.(Auth <: sessionKey).(at))[targetEntity] |
		-- if there's already a session key assigned to the target device,
		some existingKey implies {
			-- then just send that session key back
			sessionKey = existingKey
			skid = (sender.sessionKeyID.at)[sessionKey]
		} else {
			-- otherwise send a new fresh key
			sessionKey in freshKey[sender.usedKeys.at]
		}
}

-- Session key request without a prior distribution key
sig SessionKeyReqNoDistrKey extends Message {
	id : AuthID,
	skid : lone SKID,	-- if requesting a session key for a device that belongs to another Auth
	requester : Name,
	target : Name		-- entity that the requester wants to communicate to
}{
	sender in Device + Attacker
	receiver in Auth + Attacker
	content = requester + target + skid

	-- assumptions
	sender not in Attacker implies
		requester = sender.name

	this not in SessionKeyReq implies 
		(requester + target + skid) -> sender.authPublicKey[id] in encryptedWith
	this not in SessionKeyReq implies 
		-- requester must be signed with its private key
		some receiver.entityPublicKey[requester] & pairedWith[requester.encryptedWith]
}

sig SessionKeyRespNoDistrKey extends SessionKeyResp {
	authID : AuthID
}{
	content = sessionKey + distrKey + targetEntity + skid
	-- distrKey is encrypted with the entity's public key
	distrKey -> sender.entityPublicKey[responseTo.requester] in encryptedWith
	some responseTo & (SessionKeyReqNoDistrKey - SessionKeyReq)

	-- If this is the first time the distribution key is being sent out to the device,
	-- it must be fresh
	distrKey in freshKey[sender.usedKeys.at]

	-- distrKey must be signed with Auth's private key
	some receiver.authPublicKey[authID] & (pairedWith[distrKey.encryptedWith])
}

-- 3. Communication between Auths
sig AuthSessionKeyReq extends Message {
	skid : SKID,
	authID : AuthID
}{
	sender in Auth + Attacker
	receiver in Auth + Attacker

	content = skid
}

sig AuthSessionKeyResp extends Message {
	sessionKey : SymKey,
	skid : SKID,
	authID : AuthID
}{
	sender in Auth + Attacker
	receiver in Auth + Attacker

	content = sessionKey + skid
	sessionKey -> skid -> at in sender.sessionKeyID
	
	some (sessionKey -> sender.otherAuthPublicKey[authID]) & encryptedWith
}

-- 4. Communication phase (client & server)
-- Communicate using the secret session key
sig SendSecretMessage extends Message {
	to : Name
}{
	sender in Client + Attacker
	receiver in Server + Attacker

	-- assumptions
	sender not in Attacker implies {
		content in SKID + Payload
		all c : content & Payload |
			some (c -> (sender.(Device <: sessionKey).at)[to]) & encryptedWith
	}
	receiver not in Attacker implies
		receiver.name = to
}

/** Simple configuration with one Auth (AuthX) and three devices **/
one sig EV extends Device {} {
	name = MyEV
	pubKey = PubkEV
	secrets = EVSecret
	authPublicKey = MyAuthX -> PubkAuthX
	(authDistrKey.first).SymKey in MyAuthX
//	no sessionKey.first
}
one sig ChargingStation extends Device {}{
	name = MyChargingStation
	pubKey = PubkStation
	authPublicKey = MyAuthY -> PubkAuthY
	(authDistrKey.first).SymKey in MyAuthY
//	no sessionKey.first
}
one sig Attacker extends Device {} {
	name = Eve
	pubKey = PubkAttacker
	secrets = MaliciousPayload
}
one sig AuthX extends Auth {} {
	pubKey = PubkAuthX
	id = MyAuthX
	entityPublicKey = MyEV -> PubkEV + Eve -> PubkAttacker
	otherAuthPublicKey = MyAuthY -> PubkAuthY
}
one sig AuthY extends Auth {} {
	pubKey = PubkAuthY
	id = MyAuthY
	entityPublicKey = MyChargingStation -> PubkStation + Eve -> PubkAttacker
	otherAuthPublicKey = MyAuthX -> PubkAuthX
}

fact {
	-- fix the key pairs
	pair = 
		PubkEV -> PrvkEV + PrvkEV -> PubkEV +
		PubkStation -> PrvkStation + PrvkStation -> PubkStation +
		PubkAttacker -> PrvkAttacker +  PrvkAttacker -> PubkAttacker +
		PubkAuthX -> PrvkAuthX + PrvkAuthX -> PubkAuthX +
		PubkAuthY -> PrvkAuthY + PrvkAuthY -> PubkAuthY
}

/** Security properties **/

pred confidentiality {
	-- Non-attacker's secret should never be known to an attacker
	no d : Device - Attacker, s : d.secrets, t : Time |  
		knows[Attacker, s, t]
}

pred integrity {
	-- Attacker's secret should never flow into a non-attacker device
	no d : Device - Attacker, s : Attacker.secrets, t : Time |
		knows[d, s, t]	
}

/** Assumptions needed to satisfy security properties **/
pred assumptions {
	-- No two devices can share names
	all disj d1, d2 : Device | d1.name != d2.name
	-- No two entities can share public keys
	all disj e1, e2 : Entity | e1.pubKey != e2.pubKey or no (e1.pubKey + e2.pubKey)
	-- It should never be the case that a public key of one entity is a private key of another
	no disj e1, e2 : Entity |
 		some e1.pubKey and some e2.pubKey and e1.pubKey.pair = e2.pubKey
	-- Session key request can't be from one device to itself
	all m : SessionKeyReqNoDistrKey | m.requester != m.target
	-- No two devices share secrets
	all disj d1, d2 : Device | no d1.secrets & d2.secrets	
	-- No session keys in init state (not for security, but for simplification only)
	all d : Device | no d.sessionKey.first
	all a : Auth | no a.sessionKey.first
	-- Policy assumption: Eve cannot appear in the policy table
	all n1, n2 : Name | 
		n1 -> n2 in (AuthX + AuthY).policy implies Eve not in (n1 + n2)
	-- Initial distribution keys correctly configured among devices and Auths
	all d : Device, a : Auth | 
		(d.authDistrKey.first)[a.id] = (a.entityDistrKey.first)[d.name] 
	-- Each entity gets assigned a unique distribution key
	all a : Auth, n1, n2 : Name |
		n1 != n2 implies
			(a.entityDistrKey[n1] != a.entityDistrKey[n2] or no a.entityDistrKey[n1])
	-- distribution keys aren't initially shared among different devices
	all disj d1, d2 : Device, a : Auth |
		(d1.authDistrKey.first)[a.id] != (d2.authDistrKey.first)[a.id] or
		no ((d1 + d2).authDistrKey.first)[a.id]
	-- public keys are configured correctly
	all n : Name, k : AsymKey |
		n -> k in AuthX.entityPublicKey implies	
			let device = name.n | k = device.pubKey
	all d : Device, i : AuthID, k : AsymKey |
		i -> k in d.authPublicKey implies
			let auth = (Auth <: id).i | auth.pubKey = k

	/** Assumptions related to multiple Auths **/
	-- Auths don't share distribution keys
	all disj a1, a2 : Auth, t : Time |
		no (a1.entityDistrKey.t)[Name] & (a2.entityDistrKey.t)[Name]
	
	-- Keys created by distinct Auths must be different
	all disj a1, a2 : Auth, t : Time | no a1.usedKeys.t & a2.usedKeys.t
}

/** Commands **/

-- Generate some random scenario with at most 4 messages and 20 data elements
run GenerateRandomScenario {
	ChargingStation.(authDistrKey.first).SymKey in MyAuthY
} for 1 but 5 Time, 5 Message,  2 Payload, 3 Name, 13 Key///, 20 Data

run CommunicationExample {
	assumptions
	no (sender + receiver).Attacker
	-- Generate a scenario that involves transfer of some payload (s) from
	-- one device (d1) to another device (d2) such that d2 eventually 
	-- has access to s.
	some s : Payload, d1, d2 : Device, t : Time |
		s in d1.initKnowledge and s not in d2.initKnowledge and
		knows[d2, s, t]	and
		d1 + d2 in Device - Attacker	
} for 
//1 but 4 Time, 4 Message, 2 Payload, 3 Name, 11 Key
//1 but 4 Time, 4 Message, 2 Payload, 3 Name, 13 Key
//1 but 6 Time, 6 Message, 2 SKID, 2 Payload, 3 Name, 13 Key
//1 but 6 Time, 6 Message, 2 Payload, 3 Name, 13 Key
1 but 6 Time, 7 Message, 2 SKID, 2 Payload, 3 Name, 13 Key

-- Check whether there's a scenario that leads to a violation of confidentiality
check CheckConfidentiality {
	assumptions implies confidentiality
} for 
//1 but 4 Time, 4 Message, 2 Payload, 3 Name, 11 Key
//1 but 4 Time, 4 Message, 2 Payload, 3 Name, 13 Key
//1 but 5 Time, 5 Message, 2 Payload, 3 Name, 11 Key
//1 but 5 Time, 5 Message, 2 Payload, 3 Name, 13 Key
//1 but 6 Time, 6 Message, 2 Payload, 3 Name, 13 Key
//1 but 7 Time, 7 Message, 2 Payload, 3 Name, 13 Key
//1 but 5 Time, 7 Message, 2 SKID, 2 Payload, 3 Name, 13 Key
//1 but 6 Time, 6 Message, 2 SKID, 2 Payload, 3 Name, 13 Key
//1 but 7 Time, 7 Message, 2 SKID, 2 Payload, 3 Name, 13 Key
//1 but 10 Time, 10 Message, 2 SKID, 2 Payload, 3 Name, 13 Key
1 but 2 Time, 2 Message, 2 SKID, 2 Payload, 3 Name, 13 Key

-- Check the integrity property
check CheckIntegrity {
	assumptions implies integrity
} for 
//1 but 6 Time, 6 Message//, 20 Data
1 but 5 Time, 5 Message, 2 Payload, 3 Name, 13 Key

/** Some other random stuff **/

fun sendsTo : Entity -> Entity -> Time {
	{from, to : Entity, t : Time | 
		some m : at.t | from = m.sender and to = m.receiver }
}

fun relevantNodes : Entity -> Time {
	{e : Entity, t : Time |
		some m : at.t | e in m.(receiver + sender) }
}

run {
	assumptions
	some m : SessionKeyRespNoDistrKey {
		m.receiver = EV
		learns[EV, m.distrKey, m]
		m.distrKey in m.content
		learns[EV, m.sessionKey, m]
		some m2 : SessionKeyRespNoDistrKey {
			m2.receiver = ChargingStation
			m2.sessionKey = m.sessionKey
			learns[ChargingStation, m2.sessionKey, m2]
			some m3 : SendSecretMessage | let t = m3.at {
				m3.sender = EV
				m3.receiver = ChargingStation				
				m3.at in m2.at.nexts
				some m3.content & EV.secrets
				EV.secrets -> m.sessionKey in m3.encryptedWith						
				no m3.content & ChargingStation.initKnowledge
				learns[ChargingStation, EV.secrets, m3]	
				knows[ChargingStation, EV.secrets, m3.at.next]
//				some m3.content & EV.secrets
//				no SKID & m3.content
/*
				m3.content in EV.initKnowledge
				m3.content not in ChargingStation.initKnowledge
				knows[EV, m2.sessionKey, t]
				knows[ChargingStation, m2.sessionKey, t]
*/
			}
		}
	}
} for
1 but 9 Time, 9 Message, 2 SKID, 2 Payload, 3 Name, 13 Key

run {
	assumptions
	some m : SessionKeyRespNoDistrKey {
		m.receiver = EV
		learns[EV, m.distrKey, m]
		m.distrKey in m.content
		learns[EV, m.sessionKey, m]
		m.at = first.next
		some m2 : SendSecretMessage {
			m2.receiver = ChargingStation
			m2.sender = EV
			m2.at = m.at.next
			some m3 : AuthSessionKeyResp {
				m3.sender = AuthX
				m3.receiver = AuthY
				m3.sessionKey = m.sessionKey
				m3.at = m2.at.next			
				some m4 : SessionKeyRespNoDistrKey {
					m4.sender = AuthY
					m4.receiver = ChargingStation
					m4.sessionKey = m3.sessionKey
					m4.at = m3.at.next.next
					some m5 : SendSecretMessage {
						m5.sender = EV
						m5.receiver = ChargingStation
						m5.content = EV.secrets
						m5.at = m4.at.next
						EV.secrets -> m.sessionKey in m5.encryptedWith
						learns[ChargingStation, EV.secrets, m5]
					}
				}
			}
		}
	}
} for
1 but 7 Time, 7 Message, 2 SKID, 2 Payload, 3 Name, 13 Key



run {
	assumptions
	some m : SessionKeyRespNoDistrKey {
		m.receiver = EV
		learns[EV, m.distrKey, m]
		m.distrKey in m.content
		learns[EV, m.sessionKey, m]
//		m.at = first.next
		some m2 : SendSecretMessage {
			m2.receiver = ChargingStation
			m2.sender = EV
//			m2.at = m.at.next
			some m3 : AuthSessionKeyResp {
				m3.sender = AuthX
				m3.receiver = AuthY
				m3.sessionKey = m.sessionKey
//				m3.at = m2.at.next			
				some m4 : SessionKeyRespNoDistrKey {
					m4.sender = AuthY
					m4.receiver = ChargingStation
					m4.sessionKey = m3.sessionKey
//					m4.at = m3.at.next.next
					some m5 : SendSecretMessage {
						m5.sender = EV
						m5.receiver = ChargingStation
						m5.content = EV.secrets
//						m5.at = m4.at.next
						EV.secrets -> m.sessionKey in m5.encryptedWith
						learns[ChargingStation, EV.secrets, m5]
					}
				}
			}
		}
	}
} for
1 but 5 Time, 7 Message, 2 SKID, 2 Payload, 3 Name, 13 Key



run {
	some disj m1, m2 : Message, t : Time | m1.at = m2.at
} for 1 but 4 Time, 4 Message, 2 SKID, 2 Payload, 3 Name, 13 Key




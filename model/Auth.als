open util/ordering[Time]	-- impose a total ordering on "Time" objects

/**
	A model of Auth, containing:
	- generic definitions of entities and messages between them
	- data types
	- knowledge axioms (i.e., how an entity gains more knowledge through messages)

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

pred knows[e : Entity, d : Name + AuthID + Payload + Nonce + Key + SKID + Token, t : Time] {
	-- then either "d" must be in this entity's initial knowledge, or
	(d in e.initKnowledge or
	-- this entity must have received some message from which it learns "d"
	some tp : t.prevs, m : receiver.e |
		m in at.tp and learns[e, d, m])
}

// Entities (Auth or device)
abstract sig Entity {
	-- a set of data values that this entity knows in its initial state
	initKnowledge : set (Name + AuthID + Payload + Nonce + Key + SKID + Token),
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
  
	-- if there's already some distribution/session key that has been given 
	usedKeys.first = (entityDistrKey.first)[Name] + (sessionKey.first)[Name]

	all s : SymKey, id : SKID, t : Time |
		s -> id -> t in sessionKeyID implies s -> t in Name.sessionKey

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
}

// Some subset of devices are clients, others are servers
// Note that they are not necessarily disjoint
sig Client, Server in Device {}

one sig Attacker extends Device {}

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
abstract sig Token {}
abstract sig Bit {}
one sig Zero, One extends Bit {}

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

-- this predicate evaluates to true iff entity "e" can learn data "d" from message "m"
pred learns[e : Entity, d : Name + AuthID + Payload + Nonce + Key + SKID + Token, m : Message] {
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
	content : set (Name + AuthID + Payload + Nonce + Key + SKID + Token),
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

run {} for 3

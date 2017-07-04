open Auth

/**
	A model of the Auth operations related to
	key distributions
**/

-- 1. Entity registraton (skipping for now?)
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

fact AuthBehavior {
	all a : Auth {
		all m : SessionKeyReqNoDistrKey & receiver.a | 
			-- a device ("requester") can only communicate to another device ("target")
			-- if the pair appears in the policy table
			m.requester -> m.target in a.policy 

		all k : SymKey, t : Time - first | let t' = t.prev |
			-- "k" is part of a used key set at time "t" iff
			k in a.usedKeys.t iff {
				-- "k" was already in the used set in the previous time "t'", or
				k in a.usedKeys.t' or 
				-- this Auth previously sent out a response that includes "k" 
				-- as a session/distribution key
				some m : at.t' & SessionKeyResp & sender.a|
					(no (a.sessionKey.t')[m.targetEntity] and k = m.sessionKey) or
					(m in SessionKeyRespNoDistrKey and k = m.distrKey)
			}

		all n : Name, k : SymKey, t : Time - first | let t' = t.prev |
			-- (n, k) appears in the distribution key table at time "t" iff
			n -> k -> t in a.entityDistrKey iff {
				-- (n, k) already is in the table at t', or
				n -> k -> t' in a.entityDistrKey or (
				-- this Auth previously sent out a response to "n" with distribution key "k"
				some m : at.t' & SessionKeyRespNoDistrKey |
					m.sender = a and
					k = m.distrKey and 
					n = m.responseTo.requester)
			}

		all n : Name, k : SymKey, t : Time - first | let t' = t.prev |
			-- (n, k) appears in the session key table at time "t" iff
			n -> k -> t in a.sessionKey iff {
				-- (n, k) already is in the table at t', or
				n -> k -> t' in a.sessionKey or (
				-- this Auth previously sent out a response to "n" with session key "k"
				(some m : at.t' & SessionKeyResp |
					m.sender = a and
					k = m.sessionKey and 
					n in m.responseTo.(requester + target))) or
				(some m : at.t' & AuthSessionKeyResp |
					m.receiver = a and 
					k = m.sessionKey)
			}	
	}
}

fact DeviceBehavior {
	all d : Device {
		-- This device can obtain a new distribution key 
		-- only through a response from Auth
		all aid : AuthID, k : SymKey, t : Time - first | let t' = t.prev |
			aid -> k -> t in d.authDistrKey iff {
				aid -> k ->  t' in d.authDistrKey or (
					some m : at.t' & SessionKeyRespNoDistrKey |
					m.receiver = d and
					aid = m.authID and
					k = m.distrKey)
		}

		-- This device can obtain a new session key 
		-- only through a response from Auth
		all n : Name, k : SymKey, t : Time - first | let t' = t.prev |
			n -> k -> t in d.sessionKey iff {
				n -> k -> t' in d.sessionKey or (
				some m : at.t' & SessionKeyResp |
					m.receiver = d and
					n = m.targetEntity and
					k = m.sessionKey)	
			}
	}
}

run {} for 3


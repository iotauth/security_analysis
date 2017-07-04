open Auth

/**
	A model of the Auth operations related to
	migration
**/

sig MigratingAuth in Auth {
	// (n, a): Device with name "n" may migrate to "a"
	migrationPlan : Name -> AuthID,
	// list of public keys of devices that may migrate to this Auth
	migrationPubKeys : Name -> AsymKey -> Time
}

sig MigratingDevice in Device {
	migrateTo : set AuthID	
}

sig Certificate in Token {}

// An Auth issues a certificate for the public key 
// of the new Auth that devices will migrate to
sig BackupMigrateInfo extends Message {
	id : AuthID,
	cert : Certificate,
	pubKeys : Name -> AsymKey
}{	
	content = cert + pubKeys[Name]
	sender in Auth + Attacker
	receiver in Auth + Attacker
}

// Issue a token instead of a certificate
// Needed when Device can't perform public crypto
// For now, assume public crypto for all devices 
/*
sig IssueMigrationToken extends Message {}{
	sender in Auth + Attacker
	receiver in Device + Attacker
}
*/

// A migration request from a device to an Auth
sig MigrationReq extends Message {
	id : AuthID,
	name : Name,
	token : Token // verification token
}{
	sender in Device + Attacker
	receiver in Auth + Attacker
}

// A response to a migration response
sig MigrationResp extends Message {
	id : AuthID,
	name : Name,
	outcome : Bit,		// = One if request accepted
	cert : Certificate	// certificate for the new Auth
}{
	sender in Auth + Attacker
	receiver in Device + Attacker
}

run {} for 3


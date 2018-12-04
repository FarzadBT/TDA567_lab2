datatype Clearance = LOW | MID | HIGH

predicate xor(bool1 : bool, bool2 : bool)
{
    (bool1 || !bool2) && !(bool1 && !bool2)
}

class Token {
    var userID : int;
    var clearance : Clearance;
    var valid: bool;

    constructor(userID : int, clearance : Clearance)
        ensures this.userID == userID && this.clearance == clearance && valid
    {
        this.userID := userID;
        this.clearance := clearance;
        valid := true;
    }

    method invalidate()
        requires valid
        ensures !valid

        modifies `valid;
    {
        valid := false;
    }
}

class ID_Station {
    var clearance : Clearance;
    var doorState : bool;
    var alarmState : bool;

    constructor(clearance : Clearance)
        ensures this.clearance == clearance
        ensures doorState == false && alarmState == false
    {
        this.clearance := clearance;
        doorState := false;
        alarmState := false;
    }

    predicate checkClearance(t: Token)
        reads `clearance, t;
    {
        t.clearance == clearance || (t.clearance == HIGH && (clearance == LOW || clearance == MID)) || (t.clearance == MID && clearance == LOW)
    }

    method auth(token: Token, userID: int)
        requires token.valid;
        requires !doorState;
        ensures userID == token.userID && checkClearance(token) ==> doorState;
        ensures userID != token.userID || !checkClearance(token) ==> alarmState && !token.valid;
        ensures !token.valid ==> !doorState;
        ensures xor(doorState, doorState);

        modifies `doorState, `alarmState, token;
    {
        var c: bool := token.clearance == clearance || (token.clearance == HIGH && (clearance == LOW || clearance == MID)) || (token.clearance == MID && clearance == LOW);
        if userID == token.userID && c {
            openDoor();
        } else {
            alarmState := true;
            token.invalidate();
        }
    }

    method openDoor()
        requires !doorState;
        ensures doorState;

        modifies `doorState;
    {
        doorState := true;
    }

    method closeDoor()
        requires doorState;
        ensures !doorState;

        modifies `doorState;
    {
        doorState := false;
    }

}

class Enrollment_Station {
    var users : map<int, Token>;

    constructor()
        ensures |users| == 0
    {
        users := map[];
    }

    method addUser(userID: int, c: Clearance) returns (t: Token)
        requires userID !in users;
        ensures userID in users;
        ensures t.userID == userID && t.clearance == c && t.valid;
        ensures users[userID] == t;
        ensures fresh(t);

        modifies `users;
    {
        t := new Token(userID, c);
        users := users[userID := t];
    }
}

method Main() {
    var es := new Enrollment_Station();
    var t1 := es.addUser(1, HIGH);
    var id1 := new ID_Station(LOW);
    id1.auth(t1, 1);
    assert id1.doorState;
}
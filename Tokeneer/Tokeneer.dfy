datatype Clearance = LOW | MID | HIGH

class Token {
    var userID : int;
    var clearance : Clearance;
    var valid: bool;

    constructor(id : int, c : Clearance)
        requires c == HIGH || c == MID || c == LOW;
        ensures userID == id && clearance == c && valid
    {
        userID := id;
        clearance := c;
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

    constructor(c : Clearance)
        requires c == HIGH || c == MID || c == LOW;
        ensures clearance == c
        ensures !doorState && !alarmState
    {
        clearance := c;
        doorState := false;
        alarmState := false;
    }

    function method checkClearance(t: Token): bool
        reads t, this`clearance;
    {
        t.clearance == clearance || ((t.clearance == HIGH && (clearance == LOW || clearance == MID)) || (t.clearance == MID && clearance == LOW))
    }

    function method checkID(t: Token, fingerprint: int): bool
        reads t;
    {
        t.userID == fingerprint
    }

    method auth(token: Token, userID: int)
        requires !doorState;
        ensures !old(token.valid) || !checkID(token, userID) ==> !doorState && !token.valid && alarmState;
        ensures old(token.valid) && checkID(token, userID) && checkClearance(token) ==> doorState && token.valid && !alarmState;
        ensures old(token.valid) && checkID(token, userID) && !checkClearance(token) ==> !doorState && token.valid && !alarmState;

        modifies `doorState, `alarmState, token, token`valid;
    {
        if (token.valid) {
            if (!checkID(token, userID)) {
                token.invalidate();
                alarmState := true;
                return;
            }
            doorState := checkClearance(token);
            alarmState := false;
        } else {
            alarmState := true;
        }
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
        requires c == HIGH || c == MID || c == LOW;
        ensures users == old(users)[userID := t]
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
    var StationHigh := new ID_Station(HIGH);
    var StationMid := new ID_Station(MID);
    var StationLow := new ID_Station(LOW);

    var UserHigh := es.addUser(1, HIGH);
    assert UserHigh.userID == 1;
    assert UserHigh.clearance == HIGH;
    assert UserHigh.valid;
    assert es.users == map[1 := UserHigh];

    var UserMid := es.addUser(2, MID);
    assert UserMid.userID == 2;
    assert UserMid.clearance == MID;
    assert UserMid.valid;
    assert es.users == map[1 := UserHigh, 2 := UserMid];

    var UserLow := es.addUser(3, LOW);
    assert UserLow.userID == 3;
    assert UserLow.clearance == LOW;
    assert UserLow.valid;
    assert es.users == map[1 := UserHigh, 2 := UserMid, 3 := UserLow];

    //We don't really know how to make the postconditions stronger for these following tests
    
    /* Valid open of door */
    StationHigh.auth(UserHigh, 1);
    assert UserHigh.valid;
    assert StationHigh.doorState;
    assert !StationHigh.alarmState;
    StationHigh.closeDoor();
    assert !StationHigh.doorState;
    

    StationMid.auth(UserMid, 2);
    assert UserMid.valid;
    assert StationMid.doorState;
    assert !StationMid.alarmState;
    StationMid.closeDoor();
    assert !StationMid.doorState;


    StationLow.auth(UserLow, 3);
    assert UserLow.valid;
    assert StationLow.doorState;
    assert !StationLow.alarmState;
    StationLow.closeDoor();
    assert !StationLow.doorState;



    /* Invalid clearance */
    StationHigh.auth(UserMid, 2);
    assert UserHigh.valid;
    assert !StationHigh.doorState;
    assert !StationHigh.alarmState;


    StationMid.auth(UserLow, 3);
    assert UserMid.valid;
    assert !StationMid.doorState;
    assert !StationMid.alarmState;



    /* Invalid id */
    StationHigh.auth(UserHigh, 2);
    assert !UserHigh.valid;
    assert !StationHigh.doorState;
    assert StationHigh.alarmState;


    StationMid.auth(UserMid, 3);
    assert !UserMid.valid;
    assert !StationMid.doorState;
    assert StationMid.alarmState;


    StationLow.auth(UserLow, 1);
    assert !UserLow.valid;
    assert !StationLow.doorState;
    assert StationLow.alarmState;
}
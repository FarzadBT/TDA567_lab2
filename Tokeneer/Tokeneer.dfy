module Tokeneer {
    datatype Clearance = INVALID | LOW | MID | HIGH

    class Token {
        var userID : int;
        var clearance : Clearance;

        method Init(userID : int, clearance : Clearance)
            requires userID >= 0 && clearance != INVALID
            modifies this
            ensures this.userID >= 0 && this.clearance != INVALID && this.userID == userID && this.clearance == clearance
        {
            this.userID := userID;
            this.clearance := clearance;
        }

        method invalidate() 
            ensures clearance == INVALID

            modifies `clearance;
        {
            clearance := INVALID;
        }

    }

    class ID_Station {
        var doorID : int;
        var clearance : Clearance;
        var doorState : bool;
        var alarmState : bool;

        method Init(doorID : int, clearance : Clearance)
            requires doorID >= 0 && clearance != INVALID
            modifies this
            ensures this.doorID >= 0 && this.doorID == doorID && this.clearance != INVALID && this.clearance == clearance
            ensures doorState == false && alarmState == false
        {
            this.doorID := doorID;
            this.clearance := clearance;
            doorState := false;
            alarmState := false;
        }

        predicate checkClearance(t: Token) 
            reads `clearance, t;
        {
            t.clearance == clearance || (t.clearance == HIGH && (clearance == LOW || clearance == MID)) || (t.clearance == MID && clearance == LOW)
        }

        method openDoor(token: Token, userID: int)
            requires token != null;
            requires !doorState;
            ensures userID == token.userID && checkClearance(token) ==> doorState;
            ensures userID != token.userID || !checkClearance(token) ==> alarmState && token.clearance == INVALID;
            ensures token.clearance == INVALID ==> !doorState;

            modifies `doorState, token;
        {

        }

        method closeDoor()
            requires doorState;
            ensures !doorState;

            modifies `doorState;
        {

        }

    }

    class Enrollment_Station {
        var users : seq<Token>;

        method Init()
            modifies this
        {
            
        }

        method addUser(userID: int, c: Clearance) returns (t: Token)
            requires !(exists  i: int :: 0 <= i < |users| && users[i].userID == userID);
            ensures t.userID == userID && t.clearance == c;

            modifies `users;
        {

        }
    }

    method Main() {
        
    }
}
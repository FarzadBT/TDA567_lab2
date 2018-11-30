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

    }

    class Enrollment_Station {
        var users : seq<Token>;

        method Init()
        modifies this
        {
            
        }
    }
}
/* AsteriodArcadeGame
 * Author: Vathila De Silva | 20200765
 * Creation date: 2024-01-02
 */
MACHINE
    AsteriodArcadeGame
SEES
    Space
    
SETS
    ACTION = {MOVE_SUCCESSFUL, MOVE_OUT_OF_BOUND, INSUFFICIENT_POWER, ASTEROID_COLLISSION, WARP_FAILED_ASTEROID_COLLISSION, WARP_FAILED_SAME_POSITION, IMMEDIATE_WARP_STARBASE_FAILED};
    MOVEMENT = {GO_UP, GO_DOWN, GO_RIGHT, GO_LEFT, WARP};
    DOCKED = {YES, NO};
    GAME_STATUS = {GAME_WON, GAME_OVER, GAME_NOT_OVER}
    
CONSTANTS
    normalPowerDrive, warpPowerDrive, crashPowerLoss, totalPower
    
PROPERTIES
    normalPowerDrive = 5 &
    warpPowerDrive = 20 &
    crashPowerLoss = 10 &
    totalPower = 100
    
DEFINITIONS
    hasEnoughPower(cp, rp) == (cp >= rp);
    isWithinGrid(xx, yy) == (xx |-> yy : space);
    isCrash(xx, yy) == (xx |-> yy : asteroidBlocks);
    isDocked == (xShipPosition |-> yShipPosition = starBase);
    isGameFinished == isDocked or (power < normalPowerDrive);
        
VARIABLES
    xShipPosition, yShipPosition, power, asteroidCrashCount, spaceshipRoute, movements
    
INVARIANT
    xShipPosition : xAxis &
    yShipPosition : yAxis &
    xShipPosition |-> yShipPosition : emptySpace &
    power : NAT &
    asteroidCrashCount : NAT &
    spaceshipRoute : seq(emptySpace) &
    movements : seq(MOVEMENT)
    
INITIALISATION
    power := totalPower ||
    asteroidCrashCount := 0 ||
    xShipPosition := prj1(xAxis, yAxis)(homeBase) ||
    yShipPosition := prj2(xAxis, yAxis)(homeBase) ||
    spaceshipRoute := [homeBase] ||
    movements := []
    
OPERATIONS
    
    //New game
    NewGame(power1) = 
    PRE
        power1 : NAT & power1 : 5..100
    THEN
        power := power1 ||
        asteroidCrashCount := 0 ||
        xShipPosition := prj1(xAxis, yAxis)(homeBase) ||
        yShipPosition := prj2(xAxis, yAxis)(homeBase) ||
        spaceshipRoute := [homeBase]
    END;
    
    // Moving up - This operation moves the spaceship one step up the grid (y+1).
    action, movement <-- moveUp =
    PRE
        action : ACTION & movement : MOVEMENT & not((xShipPosition |-> yShipPosition = starBase) or (power < normalPowerDrive)) 
    THEN
        IF
            hasEnoughPower(power, normalPowerDrive) //this function checks if the spaceship has enough power to move
        THEN
            IF
                isWithinGrid(xShipPosition, yShipPosition + 1) //this function checks if the spaceship is within the grid
            THEN
                IF 
                    not(isCrash(xShipPosition, yShipPosition + 1))
                THEN
                    IF
                        (power - normalPowerDrive >= 0)
                    THEN
                        yShipPosition := yShipPosition + 1 ||
                        power := power - normalPowerDrive ||
                        spaceshipRoute := spaceshipRoute <- (xShipPosition |-> yShipPosition + 1) ||
                        movements := movements <- GO_UP ||
                        action := MOVE_SUCCESSFUL ||
                        movement := GO_UP
                    ELSE
                        // Avoids movements without enough power
                        yShipPosition := yShipPosition + 1 ||
                        power := 0 ||
                        spaceshipRoute := spaceshipRoute <- (xShipPosition |-> yShipPosition + 1) ||
                        movements := movements <- GO_UP ||
                        action := MOVE_SUCCESSFUL ||
                        movement := GO_UP
                    END
                ELSE
                    // If asteroid collission
                    IF
                        (power - normalPowerDrive - crashPowerLoss >= 0)
                    THEN
                        power := power - normalPowerDrive - crashPowerLoss ||
                        asteroidCrashCount := asteroidCrashCount + 1 ||
                        action := ASTEROID_COLLISSION ||
                        movement := GO_UP
                    ELSE
                         // Avoids movements without enough power
                        power := 0 ||
                        asteroidCrashCount := asteroidCrashCount + 1 ||
                        action := ASTEROID_COLLISSION ||
                        movement := GO_UP
                    END
                END
            // Position out of grid    
            ELSE
                action := MOVE_OUT_OF_BOUND
            END
        // Not enough energy to do the movement    
        ELSE
            action := INSUFFICIENT_POWER
        END
    END;
    
    // Moving down - This operation moves the spaceship one step down the grid (y-1).
    action, movement <-- moveDown =
    PRE
        action : ACTION & movement : MOVEMENT & not((xShipPosition |-> yShipPosition = starBase) or (power < normalPowerDrive)) 
    THEN
        IF
            hasEnoughPower(power, normalPowerDrive)
        THEN
            IF
                isWithinGrid(xShipPosition, yShipPosition - 1)
            THEN
                IF 
                    not(isCrash(xShipPosition, yShipPosition - 1))
                THEN
                    IF
                        (power - normalPowerDrive >= 0)
                    THEN
                        yShipPosition := yShipPosition - 1 ||
                        power := power - normalPowerDrive ||
                        spaceshipRoute := spaceshipRoute <- (xShipPosition |-> yShipPosition - 1) ||
                        movements := movements <- GO_DOWN ||
                        action := MOVE_SUCCESSFUL ||
                        movement := GO_DOWN
                    ELSE
                         // Avoids movements without enough power
                        yShipPosition := yShipPosition - 1 ||
                        power := 0 ||
                        spaceshipRoute := spaceshipRoute <- (xShipPosition |-> yShipPosition - 1) ||
                        movements := movements <- GO_DOWN ||
                        action := MOVE_SUCCESSFUL ||
                        movement := GO_DOWN
                    END
                // Asteroid collission    
                ELSE
                    IF
                        (power - normalPowerDrive - crashPowerLoss >= 0)
                    THEN
                        power := power - normalPowerDrive - crashPowerLoss ||
                        asteroidCrashCount := asteroidCrashCount + 1 ||
                        action := ASTEROID_COLLISSION ||
                        movement := GO_DOWN
                    ELSE
                         // Avoids movements without enough power
                        power := 0 ||
                        asteroidCrashCount := asteroidCrashCount + 1 ||
                        action := ASTEROID_COLLISSION ||
                        movement := GO_DOWN
                    END
                END
            // Position out of grid    
            ELSE
                action := MOVE_OUT_OF_BOUND
            END
        // If not enough power   
        ELSE
            action := INSUFFICIENT_POWER
        END   
    END;
    
    // Moves right
    action, movement <-- moveRight =
    PRE
        action : ACTION & movement : MOVEMENT & not((xShipPosition |-> yShipPosition = starBase) or (power < normalPowerDrive)) 
    THEN
        IF
            hasEnoughPower(power, normalPowerDrive)
        THEN
            IF
                isWithinGrid(xShipPosition + 1, yShipPosition)
            THEN
                IF 
                    not(isCrash(xShipPosition + 1, yShipPosition))
                THEN
                    IF
                        (power - normalPowerDrive >= 0)
                    THEN
                        xShipPosition := xShipPosition + 1 ||
                        power := power - normalPowerDrive ||
                        spaceshipRoute := spaceshipRoute <- (xShipPosition + 1 |-> yShipPosition) ||
                        movements := movements <- GO_RIGHT ||
                        action := MOVE_SUCCESSFUL ||
                        movement := GO_RIGHT
                    ELSE
                         // Avoids movements without enough power
                        xShipPosition := xShipPosition + 1 ||
                        power := 0 ||
                        spaceshipRoute := spaceshipRoute <- (xShipPosition + 1 |-> yShipPosition) ||
                        movements := movements <- GO_RIGHT ||
                        action := MOVE_SUCCESSFUL ||
                        movement := GO_RIGHT
                    END
                // Asteroid collission    
                ELSE
                    IF
                        (power - normalPowerDrive - crashPowerLoss >= 0)
                    THEN
                        power := power - normalPowerDrive - crashPowerLoss ||
                        asteroidCrashCount := asteroidCrashCount + 1 ||
                        action := ASTEROID_COLLISSION ||
                        movement := GO_RIGHT
                    ELSE
                         // Avoids movements without enough power
                        power := 0 ||
                        asteroidCrashCount := asteroidCrashCount + 1 ||
                        action := ASTEROID_COLLISSION ||
                        movement := GO_RIGHT
                    END
                END
             // Position out of grid   
            ELSE
                action := MOVE_OUT_OF_BOUND
            END
        // Not enough power to continue the movement    
        ELSE
            action := INSUFFICIENT_POWER
        END   
    END;
    
    // Moves left
    action, movement <-- moveLeft =
    PRE
        action : ACTION & movement : MOVEMENT & not((xShipPosition |-> yShipPosition = starBase) or (power < normalPowerDrive)) 
    THEN
        IF
            hasEnoughPower(power, normalPowerDrive)
        THEN
            IF
                isWithinGrid(xShipPosition - 1, yShipPosition)
            THEN
                IF 
                    not(isCrash(xShipPosition - 1, yShipPosition))
                THEN
                    IF
                        (power - normalPowerDrive >= 0)
                    THEN
                        xShipPosition := xShipPosition - 1 ||
                        power := power - normalPowerDrive ||
                        spaceshipRoute := spaceshipRoute <- (xShipPosition - 1 |-> yShipPosition) ||
                        movements := movements <- GO_LEFT ||
                        action := MOVE_SUCCESSFUL ||
                        movement := GO_LEFT
                    ELSE
                         // Avoids movements without enough power
                        xShipPosition := xShipPosition - 1 ||
                        power := 0 ||
                        spaceshipRoute := spaceshipRoute <- (xShipPosition - 1 |-> yShipPosition) ||
                        movements := movements <- GO_LEFT ||
                        action := MOVE_SUCCESSFUL ||
                        movement := GO_LEFT
                    END
                 // Asteroid collission   
                ELSE
                    IF
                        (power - normalPowerDrive - crashPowerLoss >= 0)
                    THEN
                        power := power - normalPowerDrive - crashPowerLoss ||
                        asteroidCrashCount := asteroidCrashCount + 1 ||
                        action := ASTEROID_COLLISSION ||
                        movement := GO_LEFT
                    ELSE
                         // Avoids movements without enough power
                        power := 0 ||
                        asteroidCrashCount := asteroidCrashCount + 1 ||
                        action := ASTEROID_COLLISSION ||
                        movement := GO_LEFT
                    END
                END
             // Position out of grid   
            ELSE
                action := MOVE_OUT_OF_BOUND
            END
        ELSE
            action := INSUFFICIENT_POWER
        END   
    END;
    
    // Warp Drive
    action, movement <-- warpDrive(newXPosition, newYPosition) =
    PRE
        action : ACTION & movement : MOVEMENT &
        newXPosition : NAT1 & newXPosition : 1..13 & newYPosition : NAT1 & newYPosition : 1..8 &
        not((xShipPosition |-> yShipPosition = starBase) or (power < normalPowerDrive)) 
    THEN
        IF
            hasEnoughPower(power, warpPowerDrive)
        THEN
            IF
                isWithinGrid( newXPosition, newYPosition )
            THEN
                IF
                    (newXPosition = xShipPosition & newYPosition = yShipPosition)
                THEN
                    action := WARP_FAILED_SAME_POSITION
                ELSE
                    IF 
                        (size(spaceshipRoute) = 1 & newXPosition|->newYPosition = starBase)
                    THEN
                        action := IMMEDIATE_WARP_STARBASE_FAILED
                    ELSE
                        IF 
                            not(isCrash(newXPosition, newYPosition))
                        THEN
                            IF
                                (power - warpPowerDrive >= 0)
                            THEN
                                power := power - warpPowerDrive ||
                                xShipPosition := newXPosition ||
                                yShipPosition := newYPosition ||
                                spaceshipRoute := spaceshipRoute <- (newXPosition |-> newYPosition) ||
                                movements := movements <- WARP ||
                                action := MOVE_SUCCESSFUL ||
                                movement := WARP
                            ELSE
                                 // Avoids movements without enough power
                                power := 0 ||
                                xShipPosition := newXPosition ||
                                yShipPosition := newYPosition ||
                                spaceshipRoute := spaceshipRoute <- (newXPosition |-> newYPosition) ||
                                movements := movements <- WARP ||
                                action := MOVE_SUCCESSFUL ||
                                movement := WARP
                            END
                        ELSE
                            action := WARP_FAILED_ASTEROID_COLLISSION
                        END
                    END
                END
            ELSE
                action := MOVE_OUT_OF_BOUND
            END
        ELSE
            action := INSUFFICIENT_POWER
        END        
    END;
    
    // Gets the current coordinates and info of the ship
    currentLocation, currentPower, asteroidCollisions <-- getShipStatus =
    BEGIN
        currentLocation := xShipPosition |-> yShipPosition ||
        currentPower := power ||
        asteroidCollisions := asteroidCrashCount
    END;
    
    // Gets all the coordinates that the ship has visited
    route <-- missionRoute =
    BEGIN
        route := spaceshipRoute
    END;
    
    // Checks if the spaceship is docked at starbase
    dockedStatus <-- spaceShipDockedStatus =
    PRE
        dockedStatus : DOCKED
    THEN
        IF
            (isDocked)
        THEN
            dockedStatus := YES
        ELSE
            dockedStatus := NO
        END
    END;
    
    // Gets the current status of the game
    status <-- gameStatus =
    PRE
        status : GAME_STATUS
    THEN
        IF
            (isDocked)
        THEN
            status := GAME_WON
        ELSE
            IF
                (power < normalPowerDrive)
            THEN
                status := GAME_OVER
            ELSE
                status := GAME_NOT_OVER
            END
        END
    END;
    
    // Gets all the movements of the spaceship
    allMovements <-- takenMovements =
    BEGIN
        allMovements := movements
    END;
    
    // Resets the game to it's initial values
    resetGame =
    PRE
        (xShipPosition |-> yShipPosition = starBase) or (power < normalPowerDrive)
    THEN
        power := totalPower ||
        asteroidCrashCount := 0 ||
        xShipPosition := prj1(xAxis, yAxis)(homeBase) ||
        yShipPosition := prj2(xAxis, yAxis)(homeBase) ||
        spaceshipRoute := [homeBase] ||
        movements := []
    END
END

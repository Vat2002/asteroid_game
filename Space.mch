/* Space
 * Author: Vathila De Silva | 20200765
 * Creation date: 2024-01-02
 */
MACHINE
    Space
    
CONSTANTS
    xAxis, yAxis, space, asteroidBlocks, emptySpace, homeBase, starBase
    
PROPERTIES
    // The known space
    xAxis = 1..12 &
    yAxis = 1..7 &
    space = xAxis * yAxis &
    
    // asteroidBlocks
    asteroidBlocks <: space &
    asteroidBlocks = {3|->2, 3|->5, 5|->4, 6|->7, 7|->1, 7|->5, 7|->7, 8|->3, 10|->6, 11|->2, 12|->5} &
    
    // Empty Space
    emptySpace <: space &
    emptySpace /\ asteroidBlocks = {} &
    emptySpace \/ asteroidBlocks = space &
    
    // Home base and Star Base
    homeBase : emptySpace & homeBase = 1|->1 &
    starBase : emptySpace & starBase = 6|->4
END

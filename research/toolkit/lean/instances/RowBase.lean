import SlotData_17

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- the target: the standard pair -/
def stdSt : St := ([la], [lb])

/-- the start state: the class-C row `BABaba, BBBaBaa` -/
def startSt : St := ([lB, lA, lB, la, lb, la], [lB, lB, lB, la, lB, la, la])

end Row17

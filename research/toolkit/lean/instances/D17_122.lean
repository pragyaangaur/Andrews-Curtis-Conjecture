import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 122 of the cap-17 certificate: slots 62464 .. 62975 -/
theorem chk_122 : chunkCheck 17 T stdSt 62464 512 = true := by decide +kernel

end Row17

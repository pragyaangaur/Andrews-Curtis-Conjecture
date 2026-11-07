import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 285 of the cap-17 certificate: slots 145920 .. 146431 -/
theorem chk_285 : chunkCheck 17 T stdSt 145920 512 = true := by decide +kernel

end Row17

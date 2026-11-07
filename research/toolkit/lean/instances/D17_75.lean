import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 75 of the cap-17 certificate: slots 38400 .. 38911 -/
theorem chk_75 : chunkCheck 17 T stdSt 38400 512 = true := by decide +kernel

end Row17

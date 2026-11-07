import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 40 of the cap-17 certificate: slots 20480 .. 20991 -/
theorem chk_40 : chunkCheck 17 T stdSt 20480 512 = true := by decide +kernel

end Row17

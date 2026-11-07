import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 131 of the cap-17 certificate: slots 67072 .. 67583 -/
theorem chk_131 : chunkCheck 17 T stdSt 67072 512 = true := by decide +kernel

end Row17

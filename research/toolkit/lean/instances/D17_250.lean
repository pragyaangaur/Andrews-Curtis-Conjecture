import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 250 of the cap-17 certificate: slots 128000 .. 128511 -/
theorem chk_250 : chunkCheck 17 T stdSt 128000 512 = true := by decide +kernel

end Row17

import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 275 of the cap-17 certificate: slots 140800 .. 141311 -/
theorem chk_275 : chunkCheck 17 T stdSt 140800 512 = true := by decide +kernel

end Row17

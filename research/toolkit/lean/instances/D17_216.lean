import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 216 of the cap-17 certificate: slots 110592 .. 111103 -/
theorem chk_216 : chunkCheck 17 T stdSt 110592 512 = true := by decide +kernel

end Row17

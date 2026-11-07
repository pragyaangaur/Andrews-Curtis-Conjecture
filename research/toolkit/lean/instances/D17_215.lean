import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 215 of the cap-17 certificate: slots 110080 .. 110591 -/
theorem chk_215 : chunkCheck 17 T stdSt 110080 512 = true := by decide +kernel

end Row17

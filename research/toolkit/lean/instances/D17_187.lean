import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 187 of the cap-17 certificate: slots 95744 .. 96255 -/
theorem chk_187 : chunkCheck 17 T stdSt 95744 512 = true := by decide +kernel

end Row17

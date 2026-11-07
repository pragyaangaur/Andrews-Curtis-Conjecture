import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 148 of the cap-17 certificate: slots 75776 .. 76287 -/
theorem chk_148 : chunkCheck 17 T stdSt 75776 512 = true := by decide +kernel

end Row17

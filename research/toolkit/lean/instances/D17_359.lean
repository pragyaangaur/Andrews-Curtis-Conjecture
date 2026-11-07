import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 359 of the cap-17 certificate: slots 183808 .. 184319 -/
theorem chk_359 : chunkCheck 17 T stdSt 183808 512 = true := by decide +kernel

end Row17

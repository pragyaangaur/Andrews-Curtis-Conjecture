import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 398 of the cap-17 certificate: slots 203776 .. 204287 -/
theorem chk_398 : chunkCheck 17 T stdSt 203776 512 = true := by decide +kernel

end Row17

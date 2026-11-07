import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 367 of the cap-17 certificate: slots 187904 .. 188415 -/
theorem chk_367 : chunkCheck 17 T stdSt 187904 512 = true := by decide +kernel

end Row17

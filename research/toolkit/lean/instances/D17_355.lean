import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 355 of the cap-17 certificate: slots 181760 .. 182271 -/
theorem chk_355 : chunkCheck 17 T stdSt 181760 512 = true := by decide +kernel

end Row17

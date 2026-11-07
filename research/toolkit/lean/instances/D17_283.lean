import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 283 of the cap-17 certificate: slots 144896 .. 145407 -/
theorem chk_283 : chunkCheck 17 T stdSt 144896 512 = true := by decide +kernel

end Row17

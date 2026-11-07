import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 316 of the cap-17 certificate: slots 161792 .. 162303 -/
theorem chk_316 : chunkCheck 17 T stdSt 161792 512 = true := by decide +kernel

end Row17

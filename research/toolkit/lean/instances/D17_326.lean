import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 326 of the cap-17 certificate: slots 166912 .. 167423 -/
theorem chk_326 : chunkCheck 17 T stdSt 166912 512 = true := by decide +kernel

end Row17

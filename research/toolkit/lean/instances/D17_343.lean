import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 343 of the cap-17 certificate: slots 175616 .. 176127 -/
theorem chk_343 : chunkCheck 17 T stdSt 175616 512 = true := by decide +kernel

end Row17

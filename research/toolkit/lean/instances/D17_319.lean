import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 319 of the cap-17 certificate: slots 163328 .. 163839 -/
theorem chk_319 : chunkCheck 17 T stdSt 163328 512 = true := by decide +kernel

end Row17

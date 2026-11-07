import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 369 of the cap-17 certificate: slots 188928 .. 189439 -/
theorem chk_369 : chunkCheck 17 T stdSt 188928 512 = true := by decide +kernel

end Row17

import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 5 of the cap-17 certificate: slots 2560 .. 3071 -/
theorem chk_5 : chunkCheck 17 T stdSt 2560 512 = true := by decide +kernel

end Row17

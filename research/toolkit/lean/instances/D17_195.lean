import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 195 of the cap-17 certificate: slots 99840 .. 100351 -/
theorem chk_195 : chunkCheck 17 T stdSt 99840 512 = true := by decide +kernel

end Row17

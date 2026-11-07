import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 193 of the cap-17 certificate: slots 98816 .. 99327 -/
theorem chk_193 : chunkCheck 17 T stdSt 98816 512 = true := by decide +kernel

end Row17

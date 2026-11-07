import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 318 of the cap-17 certificate: slots 162816 .. 163327 -/
theorem chk_318 : chunkCheck 17 T stdSt 162816 512 = true := by decide +kernel

end Row17

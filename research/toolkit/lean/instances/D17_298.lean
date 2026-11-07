import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 298 of the cap-17 certificate: slots 152576 .. 153087 -/
theorem chk_298 : chunkCheck 17 T stdSt 152576 512 = true := by decide +kernel

end Row17

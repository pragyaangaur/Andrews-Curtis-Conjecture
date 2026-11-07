import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 48 of the cap-17 certificate: slots 24576 .. 25087 -/
theorem chk_48 : chunkCheck 17 T stdSt 24576 512 = true := by decide +kernel

end Row17

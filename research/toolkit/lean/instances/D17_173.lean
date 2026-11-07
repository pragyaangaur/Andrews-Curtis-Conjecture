import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 173 of the cap-17 certificate: slots 88576 .. 89087 -/
theorem chk_173 : chunkCheck 17 T stdSt 88576 512 = true := by decide +kernel

end Row17

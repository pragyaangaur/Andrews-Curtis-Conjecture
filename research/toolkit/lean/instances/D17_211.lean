import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 211 of the cap-17 certificate: slots 108032 .. 108543 -/
theorem chk_211 : chunkCheck 17 T stdSt 108032 512 = true := by decide +kernel

end Row17

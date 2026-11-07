import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 509 of the cap-17 certificate: slots 260608 .. 261119 -/
theorem chk_509 : chunkCheck 17 T stdSt 260608 512 = true := by decide +kernel

end Row17

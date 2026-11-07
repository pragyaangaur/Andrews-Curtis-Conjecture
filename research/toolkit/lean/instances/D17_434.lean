import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 434 of the cap-17 certificate: slots 222208 .. 222719 -/
theorem chk_434 : chunkCheck 17 T stdSt 222208 512 = true := by decide +kernel

end Row17

import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 154 of the cap-17 certificate: slots 78848 .. 79359 -/
theorem chk_154 : chunkCheck 17 T stdSt 78848 512 = true := by decide +kernel

end Row17

import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 86 of the cap-17 certificate: slots 44032 .. 44543 -/
theorem chk_86 : chunkCheck 17 T stdSt 44032 512 = true := by decide +kernel

end Row17

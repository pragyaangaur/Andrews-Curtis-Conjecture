import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 126 of the cap-17 certificate: slots 64512 .. 65023 -/
theorem chk_126 : chunkCheck 17 T stdSt 64512 512 = true := by decide +kernel

end Row17

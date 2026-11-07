import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 80 of the cap-16 certificate: slots 81920 .. 82943 -/
theorem chk_80 : chunkCheck 16 T stdSt 81920 1024 = true := by decide +kernel

end Row16

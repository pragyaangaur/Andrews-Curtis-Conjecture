import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 119 of the cap-16 certificate: slots 121856 .. 122879 -/
theorem chk_119 : chunkCheck 16 T stdSt 121856 1024 = true := by decide +kernel

end Row16

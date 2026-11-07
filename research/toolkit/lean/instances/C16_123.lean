import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 123 of the cap-16 certificate: slots 125952 .. 126975 -/
theorem chk_123 : chunkCheck 16 T stdSt 125952 1024 = true := by decide +kernel

end Row16

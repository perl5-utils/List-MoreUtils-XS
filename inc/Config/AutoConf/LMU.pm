package inc::Config::AutoConf::LMU;

use strict;
use warnings;

use Config::AutoConf '0.315';

use base qw(Config::AutoConf);

sub check_lmu_prerequisites
{
    my $self = shift->_get_instance();

    $self->check_produce_loadable_xs_build() or die "Can't produce loadable XS module";
    $self->check_all_headers(qw(time.h sys/time.h));
    $self->check_funcs([qw(time)]);

    unless($self->check_types([qw(size_t ssize_t)]))
    {
        $self->check_sizeof_types(["int", "long", "long long", "ptr"], {
            prologue => $self->_default_includes . <<EOPTR
typedef void * ptr;
EOPTR
        });
    }
    $self->check_builtin("expect");
}

1;

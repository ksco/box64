#if !(defined(GO) && defined(GOM) && defined(GO2) && defined(DATA))
error Meh...
#endif

GO(libssh2_agent_connect, iFp)
GO(libssh2_agent_disconnect, iFp)
GO(libssh2_agent_free, vFp)
GO(libssh2_agent_get_identity, iFppp)
GO(libssh2_agent_get_identity_path, iFpppi)
GO(libssh2_agent_init, pFp)
GO(libssh2_agent_list_identities, iFp)
GO(libssh2_agent_set_identity_path, vFpp)
GO(libssh2_agent_userauth, iFppp)
GO(libssh2_banner_set, iFpp)
GO(libssh2_base64_decode, iFppppi)
GO(libssh2_channel_close, iFp)
GO(libssh2_channel_direct_tcpip_ex, iFppipi)
GO(libssh2_channel_eof, iFp)
GO(libssh2_channel_flush_ex, iFpi)
GO(libssh2_channel_forward_accept, pFp)
GO(libssh2_channel_forward_cancel, iFp)
GO(libssh2_channel_forward_listen_ex, pFppipi)
GO(libssh2_channel_free, iFp)
GO(libssh2_channel_get_exit_signal, iFppppppp)
GO(libssh2_channel_get_exit_status, iFp)
GO(libssh2_channel_handle_extended_data, vFpi)
GO(libssh2_channel_handle_extended_data2, iFpi)
GO(libssh2_channel_process_startup, iFppupu)
GO(libssh2_channel_read_ex, iFpipi)
GO(libssh2_crypt_methods, pFv)
# -*- coding: utf-8 -*-
# Part of Odoo. See LICENSE file for full copyright and licensing details.

from odoo import api, models


class AccountInvoice(models.Model):
    _inherit = 'account.invoice'

    @api.multi
    def invoice_validate(self):
        # fetch the partner's id and subscribe the partner to the invoice
        for invoice in self:
            if invoice._auto_subscribe_partner_id_on_validate():
                invoice.message_subscribe([invoice.partner_id.id])
        return super(AccountInvoice, self).invoice_validate()

    @api.multi
    def _auto_subscribe_partner_id_on_validate(self):
        self.ensure_one()
        return (
            self.partner_id not in self.message_partner_ids
        )

    @api.multi
    def get_signup_url(self):
        self.ensure_one()
        return self.partner_id.with_context(signup_valid=True)._get_signup_url_for_action(
            action='/mail/view',
            model=self._name,
            res_id=self.id)[self.partner_id.id]
